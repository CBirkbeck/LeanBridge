import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.MordellWeilGenerators
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure

/-!
# At most two torsion generators

The LMFDB describes the Mordell–Weil group `E(K)` of an elliptic curve over a number field by its
Mordell–Weil generators (LMFDB `ec.mw_generators`): `r` non-torsion generators and **up to two
torsion generators**. This file proves the bound: over a field of characteristic zero, the torsion
subgroup `E(F)_tors` has a `ℤ`-basis of at most two points, so a minimal one, the torsion generators
of `WeierstrassCurve.Affine.IsMordellWeilGenerators`, has at most two points.

The torsion subgroup is finite, of order `N` say, so it embeds in `E(F̄)[N] ≃ (ℤ/N)²` (Tau Ceti's
`WeierstrassCurve.torsion_addEquiv_prod`). A subgroup `G` of `(ℤ/N)²` has a `ℤ`-basis of at most two
elements: its preimage in `ℤ²` has a basis in Smith normal form with respect to a basis of `ℤ²`, and
the images of its vectors form a `ℤ`-basis of `G`, since the kernel `N ℤ²` of `ℤ² → (ℤ/N)²` is
compatible with every basis of `ℤ²`.

## Main results

* `WeierstrassCurve.Affine.exists_isTorsionBasis_le_two`: over a field of characteristic zero, when
  `E(F)` is finitely generated, `E(F)_tors` has a `ℤ`-basis of at most two points.
* `WeierstrassCurve.Affine.IsMordellWeilGenerators.le_two`: there are at most two torsion
  generators (LMFDB `ec.mw_generators`).
-/

open Module Submodule

namespace WeierstrassCurve.Affine

/-- The reduction `ℤ² → (ℤ/N)²`. -/
private noncomputable def reduction (N : ℕ) : (Fin 2 → ℤ) →ₗ[ℤ] ZMod N × ZMod N :=
  (((Int.castAddHom (ZMod N)).comp (Pi.evalAddMonoidHom _ 0)).prod
    ((Int.castAddHom (ZMod N)).comp (Pi.evalAddMonoidHom _ 1))).toIntLinearMap

private lemma reduction_apply (N : ℕ) (w : Fin 2 → ℤ) :
    reduction N w = ((w 0 : ZMod N), (w 1 : ZMod N)) :=
  rfl

private lemma reduction_surjective (N : ℕ) : Function.Surjective (reduction N) := fun x ↦
  ⟨![(x.1.cast : ℤ), (x.2.cast : ℤ)], by simp [reduction_apply]⟩

private lemma reduction_eq_zero {N : ℕ} {w : Fin 2 → ℤ} (hw : reduction N w = 0) :
    ∃ u, w = (N : ℤ) • u := by
  rw [reduction_apply, Prod.mk_eq_zero] at hw
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hw.1 with ⟨a, ha⟩
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hw.2 with ⟨b, hb⟩
  exact ⟨![a, b], funext fun i ↦ by fin_cases i <;> simp [ha, hb]⟩

private lemma reduction_smul (N : ℕ) (u : Fin 2 → ℤ) : reduction N ((N : ℤ) • u) = 0 := by
  simp [reduction_apply]

/-- A group embedding in `(ℤ/N)²` has a `ℤ`-basis of at most two elements. -/
private lemma exists_basis_le_two {G : Type*} [AddCommGroup G] {N : ℕ}
    (ι : G →+ ZMod N × ZMod N) (hι : Function.Injective ι) :
    ∃ s ≤ 2, ∃ g : Fin s → G, AddSubgroup.closure (Set.range g) = ⊤ ∧
      ∀ b : Fin s → ℤ, ∑ j, b j • g j = 0 → ∀ j, b j • g j = 0 := by
  let H : Submodule ℤ (Fin 2 → ℤ) := (LinearMap.range ι.toIntLinearMap).comap (reduction N)
  rcases H.smithNormalForm (Pi.basisFun ℤ (Fin 2)) with ⟨n, snf⟩
  have hg (i : Fin n) : ∃ x, ι x = reduction N (snf.bN i) := (snf.bN i).2
  choose g hg using hg
  refine ⟨n, by simpa using Fintype.card_le_of_embedding snf.f, g, eq_top_iff.mpr fun x _ ↦ ?_,
    fun b hb j ↦ ?_⟩
  · rcases reduction_surjective N (ι x) with ⟨v, hv⟩
    have hvH : v ∈ H := ⟨x, hv.symm⟩
    have hsum : ((∑ i, snf.bN.repr ⟨v, hvH⟩ i • snf.bN i : H) : Fin 2 → ℤ) = v :=
      congrArg Subtype.val (snf.bN.sum_repr ⟨v, hvH⟩)
    have hx : x = ∑ i, snf.bN.repr ⟨v, hvH⟩ i • g i := hι <| by
      rw [map_sum, ← hv]
      simp_rw [map_zsmul, hg]
      nth_rw 1 [← hsum]
      rw [Submodule.coe_sum, map_sum]
      simp_rw [Submodule.coe_smul, map_zsmul]
    exact hx ▸ sum_mem fun i _ ↦ zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · have hred : reduction N ((∑ i, b i • snf.bN i : H) : Fin 2 → ℤ) = 0 := by
      rw [Submodule.coe_sum, map_sum]
      simp_rw [Submodule.coe_smul, map_zsmul, ← hg, ← map_zsmul, ← map_sum, hb, map_zero]
    rcases reduction_eq_zero hred with ⟨u, hu⟩
    have hdvd : (N : ℤ) ∣ b j * snf.a j := by
      have h := snf.repr_apply_embedding_eq_repr_smul (∑ i, b i • snf.bN i) (i := j)
      rw [hu, LinearEquiv.map_smul, LinearEquiv.map_smul, Finsupp.smul_apply, Finsupp.smul_apply,
        snf.bN.repr_sum_self, smul_eq_mul, smul_eq_mul] at h
      exact ⟨_, (mul_comm _ _).trans h.symm⟩
    rcases hdvd with ⟨q, hq⟩
    refine hι ?_
    rw [map_zsmul, hg, map_zero, ← map_zsmul, snf.snf, smul_smul, hq, mul_smul]
    exact reduction_smul N _

variable {F : Type*} [Field F] [DecidableEq F] [CharZero F] {W : Affine F} [W.IsElliptic]

/-- **The torsion subgroup has a `ℤ`-basis of at most two points**: over a field of characteristic
zero, when `E(F)` is finitely generated, for instance over a number field, `E(F)_tors` embeds in
`E(F̄)[N] ≃ (ℤ/N)²` for its order `N`, so it has a `ℤ`-basis of at most two points. -/
lemma exists_isTorsionBasis_le_two [Module.Finite ℤ W.Point] :
    ∃ s ≤ 2, ∃ T : Fin s → W.Point, IsTorsionBasis T := by
  classical
  have : Finite (torsion ℤ W.Point) := finite_of_fg_torsion _ torsion_isTorsion
  have : Finite (AddCommGroup.torsion W.Point) := by
    rw [← torsion_int]
    exact this
  let N : ℕ := Nat.card (AddCommGroup.torsion W.Point)
  have : NeZero N := ⟨Nat.card_pos.ne'⟩
  let φ : W.Point →+ (W.baseChange (AlgebraicClosure F)).toAffine.Point :=
    (Point.baseChange (W' := W) F (AlgebraicClosure F)).comp
      (Point.equivBaseChangeSelf W).toAddMonoidHom
  have hφ : Function.Injective φ :=
    (Point.map_injective _).comp (Point.equivBaseChangeSelf W).injective
  let ψ : AddCommGroup.torsion W.Point →+
      AddSubgroup.torsionBy (W.baseChange (AlgebraicClosure F)).toAffine.Point (N : ℤ) :=
    (φ.comp (AddCommGroup.torsion W.Point).subtype).codRestrict _ fun P ↦
      AddSubgroup.torsionBy.nsmul_iff.mpr <| by
        rw [← map_nsmul, card_nsmul_eq_zero', map_zero]
  rcases (W.baseChange (AlgebraicClosure F)).torsion_addEquiv_prod N
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) with ⟨e⟩
  rcases exists_basis_le_two (e.toAddMonoidHom.comp ψ) (e.injective.comp fun P Q h ↦
    Subtype.ext (hφ (congrArg Subtype.val h))) with ⟨s, hs, g, hg, hind⟩
  refine ⟨s, hs, fun j ↦ g j, ⟨le_antisymm ((AddSubgroup.closure_le _).mpr
    (Set.range_subset_iff.mpr fun j ↦ (g j).2)) fun x hx ↦ ?_, fun b hb j ↦ ?_⟩⟩
  · have hmap :
        x ∈ (AddSubgroup.closure (Set.range g)).map (AddCommGroup.torsion W.Point).subtype :=
      AddSubgroup.mem_map_of_mem _ (hg ▸ AddSubgroup.mem_top _ :
        (⟨x, hx⟩ : AddCommGroup.torsion W.Point) ∈ AddSubgroup.closure (Set.range g))
    rwa [AddMonoidHom.map_closure, ← Set.range_comp] at hmap
  · simpa using congrArg Subtype.val (hind b (Subtype.ext (by simpa using hb)) j)

/-- **There are at most two torsion generators** among Mordell–Weil generators of an elliptic curve
over a field of characteristic zero, for instance a number field (LMFDB `ec.mw_generators`). -/
lemma IsMordellWeilGenerators.le_two [Module.Finite ℤ W.Point] {r s : ℕ} {P : Fin r → W.Point}
    {T : Fin s → W.Point} (h : IsMordellWeilGenerators P T) : s ≤ 2 := by
  rcases exists_isTorsionBasis_le_two (W := W) with ⟨t, ht, T', hT'⟩
  exact (h.le_of_isTorsionBasis t T' hT').trans ht

end WeierstrassCurve.Affine
