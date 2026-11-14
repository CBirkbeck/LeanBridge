import Mathlib.Topology.Algebra.OpenSubgroup
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.CompletedUnitsProfinite
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.Label

/-!
# The topology of the enhanced group, and the level and the index of its open subgroups

Let `(O, μ)` be a polarized order in a quaternion algebra `B` over `ℚ`. The enhanced group
`Aut_{±μ}(O) ⋉ Ô^×` (LMFDB `shimcurve.enhanced_group`, `Subalgebra.EnhancedGroup`) is a semidirect
product of the profinite group `Ô^× = lim_N (O/NO)^×` (`Subalgebra.completedUnitsTopology`) by the
group `Aut_{±μ}(O)`, which is finite for a polarized order. Its topology is the product topology
of the profinite topology on `Ô^×` and the discrete topology on `Aut_{±μ}(O)`
(`Subalgebra.enhancedGroupTopology`): the one for which `Ô^×` is an open subgroup with its profinite
topology. With it the enhanced group is a topological group, the kernels `Γ(Ô, N)` of the
reductions `Ô^× → (O/NO)^×` are open subgroups, compact when `O` is a finitely generated
`ℤ`-module, and every open subgroup `H` contains one of them.

So the level of an open subgroup `H` (LMFDB `shimcurve.level`, `Subalgebra.enhancedGroupLevel`), the
least positive integer `N` such that `H` contains `Γ(Ô, N) = ker(Ô^× → (O/NO)^×)`, exists: it is
positive, `H` contains the kernel of reduction modulo it, and it is the least such integer. When
moreover `Aut_{±μ}(O)` is finite and `O` is finitely generated, as for a polarized order of a
quaternion algebra over `ℚ` (`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.AutPmMuFinite`), the
enhanced group is compact, so its open subgroups are the open compact subgroups of LMFDB
`shimcurve.level` and `shimcurve.index`, and they have finite index, the index of the Shimura curve
`X_H` (LMFDB `shimcurve.index`, Mathlib's `Subgroup.index`).

As in `LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroup`, `B` is any `ℚ`-algebra, `O`
any subring and `μ` any element, and the enhanced group is Mathlib's `Ô^× ⋊ Aut_{±μ}(O)`. The
topology is a definition rather than an instance, as `Subalgebra.completedUnitsTopology` is.

## Main definitions

* `Subalgebra.enhancedGroupTopology` (LMFDB `shimcurve.level`, `shimcurve.index`): the topology of
  the enhanced group.

## Main results

* `Subalgebra.isTopologicalGroup_enhancedGroup`: the enhanced group is a topological group.
* `Subalgebra.isOpen_enhancedGroupKernel`: the kernel of `Ô^× → (O/NO)^×` is open in the enhanced
  group.
* `Subalgebra.isCompact_enhancedGroupKernel`: it is compact when `O` is a finitely generated
  `ℤ`-module, so open compact subgroups exist.
* `Subalgebra.exists_enhancedGroupKernel_le_of_isOpen` (LMFDB `shimcurve.level`): an open subgroup
  of the enhanced group contains the kernel of `Ô^× → (O/NO)^×` for some positive integer `N`.
* `Subalgebra.isLeast_enhancedGroupLevel` (LMFDB `shimcurve.level`): the level of an open subgroup
  `H` is the least positive integer `N` such that `H` contains the kernel of `Ô^× → (O/NO)^×`.
* `Subalgebra.enhancedGroupLevel_pos_of_isOpen` (LMFDB `shimcurve.level`): the level of an open
  subgroup is positive.
* `Subalgebra.compactSpace_enhancedGroup`: the enhanced group is compact when `O` is a finitely
  generated `ℤ`-module and `Aut_{±μ}(O)` is finite.
* `Subalgebra.isCompact_of_isOpen_enhancedGroup` (LMFDB `shimcurve.level`, `shimcurve.index`): then
  every open subgroup of the enhanced group is compact.
* `Subalgebra.finiteIndex_of_isOpen_enhancedGroup` (LMFDB `shimcurve.index`): and it has finite
  index.
-/

open SemidirectProduct Topology

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] (O : Subalgebra ℤ B) (μ : B) (N : ℕ+)
  {H : Subgroup (O.EnhancedGroup μ)}

/-- The **topology of the enhanced group** `Aut_{±μ}(O) ⋉ Ô^×` (LMFDB `shimcurve.level`,
`shimcurve.index`): the product of the profinite topology of `Ô^× = lim_N (O/NO)^×` and the discrete
topology of `Aut_{±μ}(O)`, for which `Ô^×` is an open subgroup. Its open compact subgroups are the
subgroups `H` defining the Shimura curves `X_H`. -/
@[instance_reducible]
def enhancedGroupTopology : TopologicalSpace (O.EnhancedGroup μ) :=
  letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
  letI _ : TopologicalSpace (O.autPmMu μ) := ⊥
  .induced (fun g ↦ (g.left, g.right)) inferInstance

lemma continuous_completedUnitsAction (w : O.autPmMu μ) :
    letI _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
    Continuous (O.completedUnitsAction μ w) := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  have _ : ∀ N : ℕ+, DiscreteTopology (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⟨rfl⟩
  exact continuous_induced_rng.mpr <| continuous_pi fun N ↦
    (continuous_of_discreteTopology (f := O.autPmMuQuotientUnitsAction N μ w)).comp
      ((continuous_apply N).comp continuous_subtype_val)

lemma mem_enhancedGroupKernel_iff {g : O.EnhancedGroup μ} :
    g ∈ O.enhancedGroupKernel μ N ↔ O.completedUnitsReduction N g.left = 1 ∧ g.right = 1 := by
  rw [← ker_enhancedGroupReduction, MonoidHom.mem_ker]
  exact ⟨fun h ↦ ⟨congrArg left h, congrArg right h⟩, fun h ↦ SemidirectProduct.ext h.1 h.2⟩

/-- **The enhanced group is a topological group** for the product of the profinite topology of
`Ô^×` and the discrete topology of `Aut_{±μ}(O)`, which acts on `Ô^×` by homeomorphisms. -/
lemma isTopologicalGroup_enhancedGroup :
    letI _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
    IsTopologicalGroup (O.EnhancedGroup μ) := by
  let _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
  have _ : IsTopologicalGroup O.completedUnits := O.isTopologicalGroup_completedUnits
  let _ : TopologicalSpace (O.autPmMu μ) := ⊥
  have _ : DiscreteTopology (O.autPmMu μ) := ⟨rfl⟩
  let _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
  have hind : IsInducing fun g : O.EnhancedGroup μ ↦ (g.left, g.right) := ⟨rfl⟩
  have hl : Continuous fun g : O.EnhancedGroup μ ↦ g.left := continuous_fst.comp hind.continuous
  have hr : Continuous fun g : O.EnhancedGroup μ ↦ g.right := continuous_snd.comp hind.continuous
  have hφ : Continuous fun p : O.autPmMu μ × O.completedUnits ↦ O.completedUnitsAction μ p.1 p.2 :=
    continuous_prod_of_discrete_left.mpr fun w ↦ O.continuous_completedUnitsAction μ w
  exact
    { continuous_mul := hind.continuous_iff.mpr <|
        ((hl.comp continuous_fst).mul <| hφ.comp <|
          (hr.comp continuous_fst).prodMk (hl.comp continuous_snd)).prodMk
            ((hr.comp continuous_fst).mul (hr.comp continuous_snd))
      continuous_inv := hind.continuous_iff.mpr <| (hφ.comp (hr.inv.prodMk hl.inv)).prodMk hr.inv }

/-- **The kernel of `Ô^× → (O/NO)^×` is open in the enhanced group.** -/
lemma isOpen_enhancedGroupKernel :
    IsOpen[O.enhancedGroupTopology μ] (O.enhancedGroupKernel μ N : Set (O.EnhancedGroup μ)) := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  have _ : ∀ N : ℕ+, DiscreteTopology (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⟨rfl⟩
  let _ : TopologicalSpace (O.autPmMu μ) := ⊥
  have _ : DiscreteTopology (O.autPmMu μ) := ⟨rfl⟩
  refine isOpen_induced_iff.mpr ⟨(O.completedUnitsReduction N ⁻¹' {1}) ×ˢ {1},
    ((isOpen_discrete _).preimage (O.continuous_completedUnitsReduction N)).prod
      (isOpen_discrete _), ?_⟩
  ext g
  exact (O.mem_enhancedGroupKernel_iff μ N).symm

/-- **The kernel of `Ô^× → (O/NO)^×` is compact in the enhanced group** when `O` is a finitely
generated `ℤ`-module, for instance an order: it is closed in the compact group `Ô^×`. So the
enhanced group has open compact subgroups. -/
lemma isCompact_enhancedGroupKernel [Module.Finite ℤ O] :
    letI _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
    IsCompact (O.enhancedGroupKernel μ N : Set (O.EnhancedGroup μ)) := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  have _ : ∀ N : ℕ+, DiscreteTopology (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⟨rfl⟩
  let _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
  have _ : CompactSpace O.completedUnits := O.compactSpace_completedUnits
  let _ : TopologicalSpace (O.autPmMu μ) := ⊥
  let _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
  have hind : IsInducing fun g : O.EnhancedGroup μ ↦ (g.left, g.right) := ⟨rfl⟩
  have hinl : Continuous (inl : O.completedUnits → O.EnhancedGroup μ) :=
    hind.continuous_iff.mpr (continuous_id.prodMk continuous_const)
  have hker : IsCompact ((O.completedUnitsReduction N).ker : Set O.completedUnits) :=
    (isClosed_singleton.preimage (O.continuous_completedUnitsReduction N)).isCompact
  exact hker.image hinl

/-- **An open subgroup of the enhanced group contains the kernel of `Ô^× → (O/NO)^×` for some
positive integer `N`** (LMFDB `shimcurve.level`): a basic open neighbourhood of `1` in
`Ô^× = lim_N (O/NO)^×` constrains finitely many components `N₁, …, N_k`, and the kernel modulo
`N₁ ⋯ N_k` lies in it. -/
lemma exists_enhancedGroupKernel_le_of_isOpen
    (hH : IsOpen[O.enhancedGroupTopology μ] (H : Set (O.EnhancedGroup μ))) :
    ∃ N : ℕ+, O.enhancedGroupKernel μ N ≤ H := by
  let _ : ∀ N : ℕ+, TopologicalSpace (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ := fun _ ↦ ⊥
  let _ : TopologicalSpace (O.autPmMu μ) := ⊥
  rcases isOpen_induced_iff.mp hH with ⟨t, ht, htH⟩
  have h1 : ((1 : O.completedUnits), (1 : O.autPmMu μ)) ∈ t := (Set.ext_iff.mp htH 1).mpr H.one_mem
  rcases isOpen_prod_iff.mp ht 1 1 h1 with ⟨u, v, hu, -, h1u, h1v, huv⟩
  rcases isOpen_induced_iff.mp hu with ⟨s, hs, hsu⟩
  rcases isOpen_pi_iff.mp hs 1 ((Set.ext_iff.mp hsu 1).mpr h1u) with ⟨I, U, hU, hIU⟩
  refine ⟨∏ k ∈ I, k, fun g hg ↦ ?_⟩
  rcases (O.mem_enhancedGroupKernel_iff μ _).mp hg with ⟨hgl, hgr⟩
  have hgu : g.left ∈ u := (Set.ext_iff.mp hsu g.left).mp <| hIU fun M hM ↦ by
    have hM' : (M : ℕ) ∣ (∏ k ∈ I, k : ℕ+) := PNat.dvd_iff.mp (Finset.dvd_prod_of_mem _ hM)
    have hgM : g.left.1 M = 1 := by
      rw [← g.left.2 M _ hM']
      exact (congrArg _ hgl).trans (map_one _)
    exact hgM ▸ (hU M hM).2
  have hgv : g.right ∈ v := hgr ▸ h1v
  exact (Set.ext_iff.mp htH g).mp (huv ⟨hgu, hgv⟩)

/-- **The level of an open subgroup `H` of the enhanced group is the least positive integer `N`
such that `H` contains the kernel of `Ô^× → (O/NO)^×`** (LMFDB `shimcurve.level`). -/
lemma isLeast_enhancedGroupLevel
    (hH : IsOpen[O.enhancedGroupTopology μ] (H : Set (O.EnhancedGroup μ))) :
    IsLeast {n | ∃ N : ℕ+, (N : ℕ) = n ∧ O.enhancedGroupKernel μ N ≤ H}
      (O.enhancedGroupLevel μ H) := by
  rcases O.exists_enhancedGroupKernel_le_of_isOpen μ hH with ⟨N, hN⟩
  exact ⟨Nat.sInf_mem ⟨N, N, rfl, hN⟩, fun _ hn ↦ Nat.sInf_le hn⟩

/-- **The level of an open subgroup of the enhanced group is positive** (LMFDB
`shimcurve.level`): there is a positive integer `N` such that the subgroup contains the kernel of
`Ô^× → (O/NO)^×`. -/
lemma enhancedGroupLevel_pos_of_isOpen
    (hH : IsOpen[O.enhancedGroupTopology μ] (H : Set (O.EnhancedGroup μ))) :
    0 < O.enhancedGroupLevel μ H := by
  rcases (O.isLeast_enhancedGroupLevel μ hH).1 with ⟨N, hN, -⟩
  exact N.pos.trans_eq hN

/-- **The enhanced group is compact** when `O` is a finitely generated `ℤ`-module, for instance an
order, and `Aut_{±μ}(O)` is finite: it is homeomorphic to the product of the profinite group `Ô^×`
and the finite discrete group `Aut_{±μ}(O)`. -/
lemma compactSpace_enhancedGroup [Module.Finite ℤ O] [Finite (O.autPmMu μ)] :
    letI _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
    CompactSpace (O.EnhancedGroup μ) := by
  let _ : TopologicalSpace O.completedUnits := O.completedUnitsTopology
  have _ : CompactSpace O.completedUnits := O.compactSpace_completedUnits
  let _ : TopologicalSpace (O.autPmMu μ) := ⊥
  let _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
  have hind : IsInducing (equivProd : O.EnhancedGroup μ ≃ O.completedUnits × O.autPmMu μ) := ⟨rfl⟩
  exact (equivProd.toHomeomorphOfIsInducing hind).symm.compactSpace

/-- **Every open subgroup of the enhanced group is compact** (LMFDB `shimcurve.level`,
`shimcurve.index`) when `O` is a finitely generated `ℤ`-module and `Aut_{±μ}(O)` is finite: the
open subgroups are then the open compact subgroups. -/
lemma isCompact_of_isOpen_enhancedGroup [Module.Finite ℤ O] [Finite (O.autPmMu μ)]
    (hH : IsOpen[O.enhancedGroupTopology μ] (H : Set (O.EnhancedGroup μ))) :
    letI _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
    IsCompact (H : Set (O.EnhancedGroup μ)) := by
  let _ : TopologicalSpace (O.EnhancedGroup μ) := O.enhancedGroupTopology μ
  have _ : IsTopologicalGroup (O.EnhancedGroup μ) := O.isTopologicalGroup_enhancedGroup μ
  have _ : CompactSpace (O.EnhancedGroup μ) := O.compactSpace_enhancedGroup μ
  exact (H.isClosed_of_isOpen hH).isCompact

/-- **An open subgroup of the enhanced group has finite index** (LMFDB `shimcurve.index`) when `O`
is a finitely generated `ℤ`-module and `Aut_{±μ}(O)` is finite: it contains the kernel of reduction
to the finite group `Aut_{±μ}(O) ⋉ (O/NO)^×` for some `N`. So the index of the Shimura curve `X_H`,
Mathlib's `Subgroup.index` of `H`, is a positive integer. -/
lemma finiteIndex_of_isOpen_enhancedGroup [Module.Finite ℤ O] [Finite (O.autPmMu μ)]
    (hH : IsOpen[O.enhancedGroupTopology μ] (H : Set (O.EnhancedGroup μ))) : H.FiniteIndex := by
  rcases O.exists_enhancedGroupKernel_le_of_isOpen μ hH with ⟨N, hN⟩
  have _ : Finite (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ :=
    have : Finite (O ⧸ Ideal.span {((N : ℕ) : O)}) := O.finite_quotient_span_natCast N
    inferInstance
  have _ : Finite (O.EnhancedGroupMod N μ) := Finite.of_equiv _ equivProd.symm
  have _ : (O.enhancedGroupKernel μ N).FiniteIndex :=
    O.ker_enhancedGroupReduction μ N ▸ Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le hN

end Subalgebra
