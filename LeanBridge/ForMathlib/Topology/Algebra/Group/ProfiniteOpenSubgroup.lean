import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Open subgroups and subgroups of finite index of profinite groups

An open subgroup `H` of a profinite group `G` (LMFDB `gl2.open`) has finite index, `G` being compact
(Tau Ceti's instance `OpenSubgroup.finiteIndex_toSubgroup`), and it contains an open normal subgroup
`N`, so it is the inverse image of its image in the finite quotient `G ⧸ N`. The converse fails:
not every subgroup of finite index of a profinite group is open. In the profinite group
`∏_{n ∈ ℕ} ℤ/2ℤ`, the finitely supported functions form a dense subgroup `W` not containing the
constant function `1`, and the kernel of a linear form vanishing on `W` but not at `1` has index
`2`. It is not open: an open subgroup contains the functions vanishing on some finite set `I` of
coordinates, among them the indicator of the complement of `I`, which differs from `1` by an
element of `W`.

## Main results

* `ProfiniteGrp.exists_comap_map_mk_eq` (LMFDB `gl2.open`): an open subgroup of a profinite group
  is the inverse image of its image in the quotient by an open normal subgroup, a finite group.
* `ProfiniteGrp.exists_finiteIndex_not_isOpen` (LMFDB `gl2.open`): not every subgroup of finite
  index of a profinite group is open, as in `∏_{n ∈ ℕ} ℤ/2ℤ`, written multiplicatively.
-/

open Topology

namespace ProfiniteGrp

/-- **An open subgroup of a profinite group is the inverse image of its image in a finite
quotient** (LMFDB `gl2.open`): it contains an open normal subgroup `N`, so that `G ⧸ N` is finite,
and is the inverse image of its image in `G ⧸ N`. -/
lemma exists_comap_map_mk_eq {G : ProfiniteGrp} (H : OpenSubgroup G) : ∃ N : OpenNormalSubgroup G,
    Finite (G ⧸ N.toSubgroup) ∧ ((H : Subgroup G).map (QuotientGroup.mk' N.toSubgroup)).comap
    (QuotientGroup.mk' N.toSubgroup) = H := by
  rcases exist_openNormalSubgroup_sub_open_nhds_of_one H.isOpen H.one_mem with ⟨N, hN⟩
  refine ⟨N, N.toSubgroup.quotient_finite_of_isOpen N.isOpen', ?_⟩
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  exact sup_eq_left.mpr hN

lemma one_notMem_range_lcoeFun :
    (1 : ℕ → ZMod 2) ∉ LinearMap.range (Finsupp.lcoeFun : (ℕ →₀ ZMod 2) →ₗ[ZMod 2] ℕ → ZMod 2) := by
  rintro ⟨f, hf⟩
  rcases Infinite.exists_notMem_finset f.support with ⟨n, hn⟩
  have h : f n = 1 := congrFun hf n
  exact one_ne_zero (h.symm.trans (Finsupp.notMem_support_iff.mp hn))

lemma exists_finiteIndex_not_isOpen_pi_zmod_two :
    ∃ K : AddSubgroup (ℕ → ZMod 2), K.FiniteIndex ∧ ¬IsOpen (K : Set (ℕ → ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Submodule.exists_dual_map_eq_bot_of_notMem one_notMem_range_lcoeFun inferInstance with
    ⟨φ, hφ, hW⟩
  refine ⟨φ.toAddMonoidHom.ker, inferInstance, fun hK ↦ hφ ?_⟩
  have hK₀ : (φ.toAddMonoidHom.ker : Set (ℕ → ZMod 2)) ∈ 𝓝 0 := hK.mem_nhds (zero_mem _)
  rw [nhds_pi, Filter.mem_pi'] at hK₀
  rcases hK₀ with ⟨I, t, ht, htK⟩
  have hg : φ (fun n ↦ if n ∈ I then 0 else 1) = 0 :=
    htK fun i hi ↦ by simpa [Finset.mem_coe.mp hi] using mem_of_mem_nhds (ht i)
  let f : ℕ →₀ ZMod 2 := Finsupp.onFinset I (fun n ↦ if n ∈ I then 1 else 0) fun n hn ↦ by
    by_contra h
    simp [h] at hn
  have hf : φ f = 0 := (Submodule.eq_bot_iff _).mp hW _ (Submodule.mem_map_of_mem ⟨f, rfl⟩)
  have h₁ : (1 : ℕ → ZMod 2) = ⇑f + fun n ↦ if n ∈ I then 0 else 1 := by
    ext n
    by_cases hn : n ∈ I <;> simp [f, hn]
  rw [h₁, map_add, hf, hg, add_zero]

/-- **Not every subgroup of finite index of a profinite group is open** (LMFDB `gl2.open`): the
profinite group `∏_{n ∈ ℕ} ℤ/2ℤ`, written multiplicatively, has a subgroup of index `2` that is not
open, the kernel of a linear form vanishing on the finitely supported functions but not on the
constant function `1`. -/
lemma exists_finiteIndex_not_isOpen :
    ∃ (G : ProfiniteGrp.{0}) (K : Subgroup G), K.FiniteIndex ∧ ¬IsOpen (K : Set G) := by
  rcases exists_finiteIndex_not_isOpen_pi_zmod_two with ⟨K, hK, hKo⟩
  have : TotallyDisconnectedSpace (Multiplicative (ℕ → ZMod 2)) :=
    inferInstanceAs (TotallyDisconnectedSpace (ℕ → ZMod 2))
  exact ⟨of (Multiplicative (ℕ → ZMod 2)), K.toSubgroup, ⟨hK.index_ne_zero⟩, hKo⟩

end ProfiniteGrp
