import LeanBridge.ForMathlib.AlgebraicTopology.TopologicalGenus
import LeanBridge.ForMathlib.GroupTheory.ModularGroupGenus
import Mathlib.NumberTheory.Modular
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Compactness
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Degree
import TauCeti.Analysis.Complex.Fuchsian.Compactification.LevelOne
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
import TauCeti.Analysis.Complex.Fuchsian.Cusp.Finite

/-!
# The compact Riemann surface `X(Γ)` of a finite-index subgroup of the modular group

Let `Γ` be a subgroup of finite index of `SL(2, ℤ)`, and `Γ̄` its image in `PSL(2, ℝ)`, a cofinite
Fuchsian group (Tau Ceti's `Subgroup.isCofinite_map_sl2zToPSL2R`). Adjoining to `Γ \ ℍ` the
finitely many cusp orbits of `Γ̄` gives Tau Ceti's compactified quotient
`Subgroup.CompactifiedQuotient`, with its topology defined by horodiscs at the cusps; Tau Ceti makes
it a connected Hausdorff complex manifold of dimension `1`. We prove that it is compact, so that it
is the compact Riemann surface `X(Γ)` whose genus is the genus of `Γ` (LMFDB
`group.sl2z.genus_subgroup`), and the complex points of the modular curves `X₀(N)` and `X₁(N)` for
`Γ = Γ₀(N)` and `Γ₁(N)` (LMFDB `ag.modcurve.x0`, `ag.modcurve.x1`).

The proof covers `Γ \ ℍ` by the translates `r 𝒟` of the fundamental domain `𝒟` of `SL(2, ℤ)` by
representatives `r` of the cosets of `Γ`: every orbit of `Γ` meets some `r 𝒟`. The part of `r 𝒟`
below a given height is compact, and the part above it lies in a horodisc at the cusp `r ∞` of `Γ̄`,
whose image in `Γ \ ℍ` lies in any given neighbourhood of the cusp orbit of `r ∞` once the height is
large enough, by the independence of cusp neighbourhoods from the choice of cusp datum. This is the
compactness criterion `Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations` of Tau
Ceti, which already gives the level-one case.

The genus of `Γ` is then the genus of the compact Riemann surface `X(Γ)`, its topological genus,
half the rank of `H¹(X(Γ), ℤ)` (`TopCat.topologicalGenus`). The Riemann–Hurwitz count
`ModularGroup.genus` computes it from the covering `X(Γ) → X(1)`, whose degree we identify with the
number `μ` of cosets of `±Γ`; the identification of the two genera, which needs the Euler
characteristic of a triangulated compact surface and the classification of surfaces, is not
proved.

## Main definitions

* `ModularGroup.topologicalGenus` (LMFDB `group.sl2z.genus_subgroup`): the genus of `X(Γ)`.

## Main results

* `Subgroup.compactSpace_compactifiedQuotient_map_sl2zToPSL2R`: `X(Γ)` is compact.
* `ModularGroup.degree_compactifiedQuotientMap_eq_natCard_cosets`: the covering `X(Γ) → X(1)` has
  degree `μ`, the number of cosets of `±Γ` in `SL(2, ℤ)`.
* The instances `DiscreteTopology (Γ.map sl2zToPSL2R)`, `ConnectedSpace X(Γ)` and
  `CompactSpace X(Γ)`, which with Tau Ceti's `ChartedSpace ℂ X(Γ)`, `IsManifold 𝓘(ℂ) ω X(Γ)` and
  `T2Space X(Γ)` make `X(Γ)` a compact Riemann surface.
-/

open MulAction OnePoint Set UpperHalfPlane TauCeti RiemannSurface Subgroup CuspDatum
  CompactifiedQuotient

open scoped MatrixGroups

lemma sl2zToPSL2R_smul (g : SL(2, ℤ)) (z : ℍ) : sl2zToPSL2R g • z = g • z := by
  simp

namespace Subgroup

variable (H : Subgroup SL(2, ℤ))

lemma quotientMk_smul_eq_of_mem {k : SL(2, ℤ)} (hk : k ∈ H) (z : ℍ) :
    Quotient.mk (orbitRel (H.map sl2zToPSL2R) ℍ) (k • z) =
      Quotient.mk (orbitRel (H.map sl2zToPSL2R) ℍ) z :=
  Quotient.sound ⟨⟨sl2zToPSL2R k, mem_map_of_mem _ hk⟩, sl2zToPSL2R_smul k z⟩

variable [H.FiniteIndex]

instance : DiscreteTopology (H.map sl2zToPSL2R) :=
  (isCofinite_map_sl2zToPSL2R H).discreteTopology

instance : ConnectedSpace (H.map sl2zToPSL2R).CompactifiedQuotient where
  toNonempty := ⟨ofQuotient (Quotient.mk _ I)⟩

lemma isCuspPoint_map_sl2zToPSL2R_smul_infty (g : SL(2, ℤ)) :
    (H.map sl2zToPSL2R).IsCuspPoint (sl2zToPSL2R g • (∞ : OnePoint ℝ)) := by
  refine (isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty H _).mpr ?_
  rw [← range_sl2zToPSL2R_eq_range_psl2zToPSL2R]
  exact ⟨⟨sl2zToPSL2R g, g, rfl⟩, rfl⟩

lemma exists_quotientMk_smul_mem_image_horodisc (A : (H.map sl2zToPSL2R).CuspOrbit → ℝ)
    (g : SL(2, ℤ)) : ∃ T : ℝ, ∀ w : ℍ, T < w.im → ∃ C : (H.map sl2zToPSL2R).CuspOrbit,
      Quotient.mk (orbitRel (H.map sl2zToPSL2R) ℍ) (g • w) ∈
        Quotient.mk (orbitRel (H.map sl2zToPSL2R) ℍ) '' horodisc C.cuspDatum (A C) := by
  rcases (isCuspPoint_map_sl2zToPSL2R_smul_infty H g).exists_cuspDatum
    (inv_smul_smul (sl2zToPSL2R g) _) with ⟨D, -, hD⟩
  rcases exists_cuspNhd_subset D D.cuspOrbit.cuspOrbit_cuspDatum (A D.cuspOrbit) with ⟨T, hT⟩
  refine ⟨T, fun w hw ↦ ⟨D.cuspOrbit, (ofQuotient_mem_cuspNhd_iff _ _).mp <|
    hT <| (ofQuotient_mem_cuspNhd_iff D T).mpr ⟨g • w, ?_, rfl⟩⟩⟩
  rwa [mem_horodisc, hD, ← sl2zToPSL2R_smul, inv_smul_smul]

/-- **The compactified quotient `X(Γ) = Γ \ ℍ*` of a finite-index subgroup `Γ` of `SL(2, ℤ)` is
compact**: every orbit of `Γ` meets a translate `r 𝒟` of the fundamental domain of `SL(2, ℤ)` by a
coset representative `r`, whose part below a given height is compact and whose part above it lies
in a horodisc at the cusp `r ∞`. -/
lemma compactSpace_compactifiedQuotient_map_sl2zToPSL2R :
    CompactSpace (H.map sl2zToPSL2R).CompactifiedQuotient := by
  have : Finite (H.map sl2zToPSL2R).CuspOrbit := (isCofinite_map_sl2zToPSL2R H).finite_cuspOrbit
  refine compactSpace_of_compact_truncations (fun C ↦ C.cuspDatum) (fun C ↦ C.cuspOrbit_cuspDatum)
    fun A ↦ ?_
  choose T hT using fun q : SL(2, ℤ) ⧸ H ↦ exists_quotientMk_smul_mem_image_horodisc H A q.out⁻¹
  refine ⟨⋃ q : SL(2, ℤ) ⧸ H,
    (sl2zToPSL2R q.out⁻¹ • ·) '' ModularGroup.truncatedFundamentalDomain (T q),
    isCompact_iUnion fun q ↦ (ModularGroup.isCompact_truncatedFundamentalDomain _).image
      (continuous_const_smul _), fun p ↦ ?_⟩
  induction p using Quotient.inductionOn with
  | h z =>
    rcases ModularGroup.exists_smul_mem_fd z with ⟨g, hg⟩
    have hk : (QuotientGroup.mk g : SL(2, ℤ) ⧸ H).out⁻¹ * g ∈ H :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
    rw [← quotientMk_smul_eq_of_mem H hk, mul_smul]
    by_cases hz : (g • z).im ≤ T (QuotientGroup.mk g)
    · exact .inl ⟨_, mem_iUnion.mpr ⟨_, g • z, ⟨hg, hz⟩, sl2zToPSL2R_smul _ _⟩, rfl⟩
    · exact .inr (hT _ _ (lt_of_not_ge hz))

instance : CompactSpace (H.map sl2zToPSL2R).CompactifiedQuotient :=
  compactSpace_compactifiedQuotient_map_sl2zToPSL2R H

end Subgroup

namespace ModularGroup

variable (Γ : Subgroup SL(2, ℤ))

lemma map_sl2zToPSL2R_le_range : Γ.map sl2zToPSL2R ≤ psl2zToPSL2R.range :=
  range_sl2zToPSL2R_eq_range_psl2zToPSL2R ▸ Γ.map_le_range sl2zToPSL2R

lemma relIndex_map_sl2zToPSL2R :
    (Γ.map sl2zToPSL2R).relIndex psl2zToPSL2R.range = Nat.card (Cosets Γ) := by
  rw [← range_sl2zToPSL2R_eq_range_psl2zToPSL2R, MonoidHom.range_eq_map, relIndex_map_map,
    top_sup_eq, relIndex_top_right, sl2zToPSL2R_ker]
  rfl

variable [Γ.FiniteIndex]

/-- **The number `μ` of cosets of `±Γ` in `SL(2, ℤ)` is the degree of the covering
`X(Γ) → X(1)`** of compact Riemann surfaces, the term `μ` of the Riemann–Hurwitz count
`ModularGroup.genus`: by Tau Ceti's `Subgroup.degree_compactifiedQuotientMap`, the degree is the
index of the image of `Γ` in that of `SL(2, ℤ)` in `PSL(2, ℝ)`, whose kernel is `{±1}`. -/
lemma degree_compactifiedQuotientMap_eq_natCard_cosets :
    degree (compactifiedQuotientMap (map_sl2zToPSL2R_le_range Γ)) = Nat.card (Cosets Γ) := by
  have : (Γ.map sl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range :=
    ⟨(relIndex_map_sl2zToPSL2R Γ).trans_ne Nat.card_pos.ne'⟩
  rw [degree_compactifiedQuotientMap, ← relIndex, relIndex_map_sl2zToPSL2R]

/-- The **genus** (LMFDB `group.sl2z.genus_subgroup`) of a finite-index subgroup `Γ` of the modular
group: the genus of the compact Riemann surface `X(Γ)` obtained by adjoining the cusps of `Γ` to
`Γ \ ℍ` (compact by `Subgroup.compactSpace_compactifiedQuotient_map_sl2zToPSL2R`), that is, its
topological genus, half the rank of `H¹(X(Γ), ℤ)`. The Riemann–Hurwitz formula identifies it with
the combinatorial count `ModularGroup.genus`, `1 + μ/12 - ν₂/4 - ν₃/3 - ν∞/2`; this identification
is not formalised. -/
noncomputable def topologicalGenus : ℕ :=
  (TopCat.of (Γ.map sl2zToPSL2R).CompactifiedQuotient).topologicalGenus

end ModularGroup
