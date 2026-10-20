import LeanBridge.ForMathlib.Analysis.Complex.UpperHalfPlane.Completed
import Mathlib.NumberTheory.Modular

/-!
# Fundamental domains of subgroups of the modular group

A closed subset `F` of the completed upper half-plane `ℍ* = ℍ ∪ ℚ ∪ {∞}` is a fundamental domain for
a subgroup `G` of `SL(2, ℤ)` when every point of the upper half-plane `ℍ` can be moved into `F` by
`G`, and distinct `G`-equivalent points of `F` lie on its boundary. This is the topological notion
of the LMFDB, as opposed to the measure-theoretic `MeasureTheory.IsFundamentalDomain`.

## Main definitions

* `ModularGroup.IsFundamentalDomain` (LMFDB `group.fuchsian.fundamental_domain`).

## Main results

* `ModularGroup.isFundamentalDomain_fd`: the standard domain `𝒟`, together with the cusp `∞`, is a
  fundamental domain for `SL(2, ℤ)`.
-/

open UpperHalfPlane UpperHalfPlane.Completed Filter OnePoint Set
open scoped MatrixGroups Modular

namespace ModularGroup

variable {G : Subgroup SL(2, ℤ)} {F : Set Completed}

variable (G F) in
/-- A set `F ⊆ ℍ* = ℍ ∪ ℚ ∪ {∞}` is a **fundamental domain** for a subgroup `G` of `SL(2, ℤ)`
(LMFDB `group.fuchsian.fundamental_domain`) if it is closed in the completed upper half-plane
`ℍ*`, every point of `ℍ` is moved into `F` by an element of `G`, and two distinct points of `F` that
are `G`-equivalent both lie on the boundary of `F`
(`ModularGroup.IsFundamentalDomain.mem_frontier` and
`ModularGroup.IsFundamentalDomain.smul_mem_frontier`). -/
structure IsFundamentalDomain : Prop where
  /-- A fundamental domain is closed. -/
  isClosed : IsClosed F
  /-- Every point of `ℍ` is `G`-equivalent to a point of a fundamental domain. -/
  exists_smul_mem (z : ℍ) : ∃ g ∈ G, g • ofUpperHalfPlane z ∈ F
  /-- A point of a fundamental domain that is `G`-equivalent to another point of it lies on its
  boundary. -/
  mem_frontier {z : Completed} {g : SL(2, ℤ)} (hz : z ∈ F) (hg : g ∈ G) (hgz : g • z ∈ F)
    (hne : g • z ≠ z) : z ∈ frontier F

lemma IsFundamentalDomain.smul_mem_frontier (hF : IsFundamentalDomain G F) {z : Completed}
    {g : SL(2, ℤ)} (hz : z ∈ F) (hg : g ∈ G) (hgz : g • z ∈ F) (hne : g • z ≠ z) :
    g • z ∈ frontier F :=
  hF.mem_frontier hgz (inv_mem hg) (by rwa [inv_smul_smul]) (by rwa [inv_smul_smul, ne_comm])

lemma preimage_ofUpperHalfPlane_fd :
    ofUpperHalfPlane ⁻¹' (ofUpperHalfPlane '' 𝒟 ∪ {cusp ∞}) = 𝒟 := by
  ext z
  simp only [mem_preimage, mem_union, mem_singleton_iff, reduceCtorEq, or_false]
  exact ⟨fun ⟨w, hw, h⟩ ↦ ofUpperHalfPlane.inj h ▸ hw, fun hz ↦ ⟨z, hz, rfl⟩⟩

lemma isClosed_fd_union_infty : IsClosed (ofUpperHalfPlane '' 𝒟 ∪ {cusp ∞}) := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_)
  cases x with
  | ofUpperHalfPlane z =>
    have hz : z ∉ 𝒟 := fun hz ↦ hx (Or.inl ⟨z, hz, rfl⟩)
    rw [nhds_ofUpperHalfPlane, mem_map, preimage_compl, preimage_ofUpperHalfPlane_fd]
    exact isClosed_fd.isOpen_compl.mem_nhds hz
  | cusp c =>
    cases c with
    | infty => exact absurd (Or.inr rfl) hx
    | coe r =>
      refine (hasBasis_nhds_ratCast r).mem_iff.mpr ⟨1 / 4, by norm_num, ?_⟩
      rintro _ (rfl | ⟨z, hz, rfl⟩)
      · exact hx
      · rw [mem_compl_iff, ← mem_preimage, preimage_ofUpperHalfPlane_fd]
        intro hzD
        have hz' : ‖(z : ℂ) - (r + ((1 / 4 : ℝ) : ℂ) * Complex.I)‖ < 1 / 4 := by
          rw [← Complex.dist_eq]
          exact hz
        have h : |z.im - 4⁻¹| < 4⁻¹ := by simpa using (Complex.abs_im_le_norm _).trans_lt hz'
        have h3 : 3 ≤ 4 * z.im ^ 2 := three_le_four_mul_im_sq_of_mem_fd hzD
        nlinarith [(abs_lt.mp h).2, z.im_pos]

lemma mem_frontier_fd_union_infty {z : ℍ} (hz : z ∈ 𝒟) (hz' : z ∉ 𝒟ᵒ) :
    ofUpperHalfPlane z ∈ frontier (ofUpperHalfPlane '' 𝒟 ∪ {cusp ∞}) := by
  rw [isClosed_fd_union_infty.frontier_eq]
  refine ⟨Or.inl ⟨z, hz, rfl⟩, fun hint ↦ hz' ?_⟩
  rw [mem_interior_iff_mem_nhds, nhds_ofUpperHalfPlane, mem_map, preimage_ofUpperHalfPlane_fd]
    at hint
  rw [fdo_eq_interior_fd]
  exact mem_interior_iff_mem_nhds.mpr hint

/-- **The standard domain `𝒟`, together with the cusp `∞`, is a fundamental domain for
`SL(2, ℤ)`**: every point of `ℍ` can be moved into `𝒟`, and an element of `SL(2, ℤ)` moving a point
of the interior `𝒟ᵒ` into `𝒟` is `±1`. -/
lemma isFundamentalDomain_fd : IsFundamentalDomain ⊤ (ofUpperHalfPlane '' 𝒟 ∪ {cusp ∞}) where
  isClosed := isClosed_fd_union_infty
  exists_smul_mem z :=
    (exists_smul_mem_fd z).imp fun g hg ↦ ⟨Subgroup.mem_top g, Or.inl ⟨g • z, hg, rfl⟩⟩
  mem_frontier {x g} hx _ hgx hne := by
    rcases hx with ⟨w, hw, rfl⟩ | hx
    · rw [smul_ofUpperHalfPlane] at hgx hne
      have hgw : g • w ∈ 𝒟 := preimage_ofUpperHalfPlane_fd.subset hgx
      have hne' : g • w ≠ w := fun h ↦ hne (congrArg ofUpperHalfPlane h)
      refine mem_frontier_fd_union_infty hw fun hw' ↦ hne' ?_
      rcases eq_one_or_neg_one_of_mem_fdo_mem_fd hw' hgw with rfl | rfl <;> simp
    · rw [mem_singleton_iff] at hx
      subst hx
      rcases hgx with ⟨w, -, hw⟩ | hgx
      · simp at hw
      · exact absurd hgx hne

end ModularGroup
