import Mathlib.GroupTheory.Commensurable
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Matrix
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.ShimuraVariety

/-!
# Connected Shimura varieties

The knowl LMFDB `ag.shimura_variety` defines the **connected Shimura varieties** as the quotients
`Γ \ M` of Hermitian symmetric domains `M` (`IsHermitianSymmetricDomain`) by torsion-free subgroups
`Γ` of the group of holomorphic automorphisms of `M`. As the knowl leaves implicit, `Γ` must be
arithmetic: in Milne's definition (*Introduction to Shimura varieties*, §3), a subgroup `Γ` of
`Hol(M)⁺` is arithmetic when there are an algebraic group `G` over `ℚ` and a surjective
homomorphism `φ : G(ℝ)⁺ → Hol(M)⁺` of Lie groups with compact kernel such that `Γ` is commensurable
with `φ(G(ℤ) ∩ G(ℝ)⁺)`; without this condition `Γ \ M` need not even be Hausdorff.

Here an algebraic group over `ℚ` is given, through a faithful representation, as a subgroup `G` of
`GL_n(ℂ)` that is the zero locus of polynomials with rational coefficients in the entries; its real
points `G(ℝ)` are the real matrices in `G`, with the topology of `GL_n(ℝ)`, and its integral points
`G(ℤ)` are those in `GL_n(ℤ)`. The Lie group `Hol(M)` is given the compact-open topology, which is
its Lie group topology by H. Cartan's theorem, and `Hol(M)⁺` is its identity component;
homomorphisms of Lie groups are the continuous homomorphisms. A connected Shimura variety is then
`Γ \ M` for a torsion-free arithmetic subgroup `Γ ≤ Hol(M)⁺`. Milne also calls these arithmetic
locally symmetric varieties, and reserves the name connected Shimura variety for the quotients by
congruence subgroups, of which the knowl says nothing. That such a quotient is an algebraic variety
(Baily-Borel) is not proved here.

## Main definitions

* `Subgroup.IsDefinedOverRat`: a subgroup of `GL_n(ℂ)` is the group of complex points of an
  algebraic subgroup of `GL_n` over `ℚ`.
* `Subgroup.realPoints` and `Subgroup.integralPoints`: its groups of real and integral points.
* `biholomorphismGroupTopology`: the compact-open topology on the holomorphic automorphisms.
* `IsArithmeticSubgroup` (LMFDB `ag.shimura_variety`): an arithmetic subgroup of the holomorphic
  automorphisms of a complex manifold.
* `IsConnectedShimuraVarietyGroup` and `ConnectedShimuraVariety` (LMFDB `ag.shimura_variety`): a
  connected Shimura variety `Γ \ M`.

## Main results

* `Subgroup.isDefinedOverRat_ker_det`: `SL_n` is an algebraic group over `ℚ`.
* `IsArithmeticSubgroup.of_le`: a subgroup of finite index of an arithmetic subgroup is
  arithmetic.
* `IsConnectedShimuraVarietyGroup.of_le`: a subgroup of finite index of a group giving a connected
  Shimura variety gives a connected Shimura variety.
* `isConnectedShimuraVarietyGroup_bot_ball_zero`: a point is a connected Shimura variety, of
  dimension `0`.
-/

open Matrix Metric MulAction Subgroup TopologicalSpace

namespace Subgroup

variable {n : ℕ} (G : Subgroup (GL (Fin n) ℂ))

/-- A subgroup `G` of `GL_n(ℂ)` is **defined over `ℚ`** if it is the zero locus in `GL_n(ℂ)` of a
set of polynomials with rational coefficients in the `n²` entries. These are the groups of complex
points of the algebraic subgroups of `GL_n` over `ℚ`, that is, of the linear algebraic groups over
`ℚ` with a faithful representation: in characteristic `0` an algebraic group is reduced and is
determined by its complex points. -/
def IsDefinedOverRat : Prop :=
  ∃ S : Set (MvPolynomial (Fin n × Fin n) ℚ), ∀ g : GL (Fin n) ℂ,
    g ∈ G ↔ ∀ p ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n ↦ g.1 ij.1 ij.2) p = 0

/-- The group `G(ℝ)` of **real points** of a subgroup `G` of `GL_n(ℂ)`: the real invertible
matrices that lie in `G`, a closed subgroup of `GL_n(ℝ)` when `G` is defined over `ℚ`. -/
noncomputable def realPoints : Subgroup (GL (Fin n) ℝ) :=
  G.comap (GeneralLinearGroup.map (algebraMap ℝ ℂ))

/-- The group `G(ℤ)` of **integral points** of a subgroup `G` of `GL_n(ℂ)`, as a subgroup of the
group `G(ℝ)` of real points: the matrices of `G(ℝ)` in `GL_n(ℤ)`, with integral entries and integral
inverse. -/
noncomputable def integralPoints : Subgroup G.realPoints :=
  (GeneralLinearGroup.map (Int.castRingHom ℝ)).range.subgroupOf G.realPoints

/-- **`SL_n` is an algebraic group over `ℚ`**: the subgroup of `GL_n(ℂ)` of the matrices of
determinant `1` is the zero locus of the polynomial `det X - 1` with integral coefficients. -/
lemma isDefinedOverRat_ker_det :
    (GeneralLinearGroup.det : GL (Fin n) ℂ →* ℂˣ).ker.IsDefinedOverRat := by
  refine ⟨{(mvPolynomialX (Fin n) (Fin n) ℚ).det - 1}, fun g ↦ ?_⟩
  rw [Set.forall_mem_singleton, map_sub, map_one, AlgHom.map_det, mvPolynomialX_mapMatrix_aeval,
    sub_eq_zero, MonoidHom.mem_ker, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]

end Subgroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Type*) [TopologicalSpace M]
  [ChartedSpace E M] (Γ : Subgroup (biholomorphismGroup (E := E) M))

/-- The **compact-open topology** on the group `Hol(M)` of holomorphic automorphisms of a complex
manifold `M`, induced by the inclusion into the continuous maps `M → M`. For a Hermitian symmetric
domain, `Hol(M)` is a Lie group and this is its topology (H. Cartan). -/
abbrev biholomorphismGroupTopology : TopologicalSpace (biholomorphismGroup (E := E) M) :=
  .induced (fun f ↦ (⟨f.1, f.2.1.continuous⟩ : C(M, M))) ContinuousMap.compactOpen

/-- A subgroup `Γ` of the group `Hol(M)` of holomorphic automorphisms of a complex manifold `M` is
**arithmetic** (LMFDB `ag.shimura_variety`; Milne, *Introduction to Shimura varieties*, §3) if there
are an algebraic group `G` over `ℚ`, given as a subgroup of `GL_n(ℂ)` defined over `ℚ`, and a
continuous homomorphism `φ` from the identity component `G(ℝ)⁺` of its real points onto the identity
component `Hol(M)⁺` of `Hol(M)` for the compact-open topology, with compact kernel, such that `Γ`
lies in `Hol(M)⁺` and is commensurable with the image `φ(G(ℤ) ∩ G(ℝ)⁺)` of the integral points. -/
def IsArithmeticSubgroup : Prop :=
  letI : TopologicalSpace (biholomorphismGroup (E := E) M) := biholomorphismGroupTopology M
  ∃ (n : ℕ) (G : Subgroup (GL (Fin n) ℂ))
    (φ : Subgroup.connectedComponentOfOne G.realPoints →* biholomorphismGroup (E := E) M),
    G.IsDefinedOverRat ∧ Continuous φ ∧
      IsCompact (φ.ker : Set (Subgroup.connectedComponentOfOne G.realPoints)) ∧
      Set.range φ = connectedComponent 1 ∧ Γ ≤ φ.range ∧
      Γ.Commensurable ((G.integralPoints.subgroupOf (Subgroup.connectedComponentOfOne _)).map φ)

/-- A subgroup `Γ` of the holomorphic automorphisms of `M` **gives a connected Shimura variety**
`Γ \ M` (LMFDB `ag.shimura_variety`) if `M` is a Hermitian symmetric domain and `Γ` is a
torsion-free arithmetic subgroup. -/
def IsConnectedShimuraVarietyGroup : Prop :=
  IsHermitianSymmetricDomain (E := E) M ∧ IsMulTorsionFree Γ ∧ IsArithmeticSubgroup M Γ

/-- The quotient `Γ \ M` of a complex manifold `M` by a group `Γ` of holomorphic automorphisms, with
the quotient topology: a **connected Shimura variety** (LMFDB `ag.shimura_variety`) when `M` is a
Hermitian symmetric domain and `Γ` a torsion-free arithmetic subgroup
(`IsConnectedShimuraVarietyGroup`). -/
abbrev ConnectedShimuraVariety : Type _ :=
  orbitRel.Quotient Γ M

variable {M Γ} {Γ' : Subgroup (biholomorphismGroup (E := E) M)}

/-- **A subgroup of finite index of an arithmetic subgroup is arithmetic**, being commensurable
with it. -/
lemma IsArithmeticSubgroup.of_le (hΓ : IsArithmeticSubgroup M Γ) (hle : Γ' ≤ Γ)
    [Γ'.IsFiniteRelIndex Γ] : IsArithmeticSubgroup M Γ' := by
  rcases hΓ with ⟨n, G, φ, hG, hφ, hker, hrange, hΓφ, hcomm⟩
  have h : Γ'.Commensurable Γ :=
    ⟨inferInstance, ⟨ne_of_eq_of_ne (Subgroup.relIndex_eq_one.mpr hle) one_ne_zero⟩⟩
  exact ⟨n, G, φ, hG, hφ, hker, hrange, hle.trans hΓφ, h.trans hcomm⟩

/-- **A subgroup of finite index of a group giving a connected Shimura variety gives a connected
Shimura variety**: it is torsion-free and arithmetic. -/
lemma IsConnectedShimuraVarietyGroup.of_le (hΓ : IsConnectedShimuraVarietyGroup M Γ)
    (hle : Γ' ≤ Γ) [Γ'.IsFiniteRelIndex Γ] : IsConnectedShimuraVarietyGroup M Γ' := by
  have hΓ₁ : IsMulTorsionFree Γ := hΓ.2.1
  exact ⟨hΓ.1, (Subgroup.inclusion_injective hle).isMulTorsionFree (Subgroup.inclusion hle),
    hΓ.2.2.of_le hle⟩

/-- **A point is a connected Shimura variety**, of dimension `0`: the unit ball of `ℂ⁰`, a point, is
a Hermitian symmetric domain, and its trivial group of holomorphic automorphisms is a torsion-free
arithmetic subgroup, for the trivial algebraic group `GL₀` over `ℚ`. -/
lemma isConnectedShimuraVarietyGroup_bot_ball_zero : IsConnectedShimuraVarietyGroup (E := Fin 0 → ℂ)
    (⟨ball 0 1, isOpen_ball⟩ : Opens (Fin 0 → ℂ)) ⊥ := by
  have hsub : Subsingleton
      (biholomorphismGroup (E := Fin 0 → ℂ) (⟨ball 0 1, isOpen_ball⟩ : Opens (Fin 0 → ℂ))) :=
    ⟨fun f g ↦ Subtype.ext (Equiv.ext fun x ↦ Subsingleton.elim _ _)⟩
  let _ : TopologicalSpace
      (biholomorphismGroup (E := Fin 0 → ℂ) (⟨ball 0 1, isOpen_ball⟩ : Opens (Fin 0 → ℂ))) :=
    biholomorphismGroupTopology _
  refine ⟨isHermitianSymmetricDomain_polydisc, ?_, ?_⟩
  · exact isMulTorsionFree_iff_not_isOfFinOrder.mpr fun a ha _ ↦ ha (Subsingleton.elim a 1)
  · exact ⟨0, ⊤, 1, ⟨∅, fun g ↦ by simp⟩, continuous_const,
      Set.subsingleton_of_subsingleton.isCompact, Set.eq_of_subset_of_subset
        (fun x _ ↦ Subsingleton.elim x 1 ▸ mem_connectedComponent)
        fun x _ ↦ ⟨1, Subsingleton.elim _ _⟩,
      bot_le, Commensurable.bot_left_iff.mpr (Finite.of_injective _ Subtype.val_injective)⟩
