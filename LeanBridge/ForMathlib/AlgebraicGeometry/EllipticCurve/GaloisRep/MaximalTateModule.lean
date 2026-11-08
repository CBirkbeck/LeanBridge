import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Maximal

/-!
# Maximal `ℓ`-adic Galois representations without complex multiplication

Without potential complex multiplication the geometric endomorphisms of an elliptic curve are the
integers, which act on the Tate module `T_ℓ E` by scalars. So `Aut_O(T_ℓ E)` is all of
`Aut(T_ℓ E)`, and the `ℓ`-adic representation is maximal exactly when its image contains
`SL₂(ℤ_ℓ)`, the first definition of the LMFDB.

## Main results

* `WeierstrassCurve.tateModuleGeometricEndCentralizer_eq_top`: without potential complex
  multiplication, `Aut_O(T_ℓ E)` is all of `Aut(T_ℓ E)`.
* `WeierstrassCurve.isMaximalTateModuleGaloisRepresentation_iff_of_not_hasGeometricCM`: without
  potential complex multiplication, the `ℓ`-adic representation is maximal exactly when its image
  contains every automorphism of determinant `1`.
-/

open Module TauCeti Isogeny

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq (SeparableClosure F)] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]

lemma mapLinearMap_pointMapHom_intCast (n : ℤ) :
    TateModule.mapLinearMap (p := ℓ) (n : W.GeometricEnd).pointMapHom = n := by
  refine LinearMap.ext fun x ↦ TateModule.ext fun k ↦ Subtype.ext ?_
  simp only [TateModule.mapLinearMap_apply, TateModule.proj_map, TateModule.levelMap_apply,
    Hom.pointMapHom_apply, End.intCast_apply, map_zsmul, AddSubgroupClass.coe_zsmul]
  rw [← zsmul_one, Hom.zsmul_pointMap, Hom.one_def, Hom.id_pointMap]

/-- **Without potential complex multiplication, `Aut_O(T_ℓ E)` is all of `Aut(T_ℓ E)`**: the
geometric endomorphisms are integers, which act on the Tate module by scalars. -/
lemma tateModuleGeometricEndCentralizer_eq_top (h : ¬W.HasGeometricCM) :
    W.tateModuleGeometricEndCentralizer ℓ = ⊤ := by
  have hS : Submonoid.centralizer (Set.range fun f : W.GeometricEnd ↦
      TateModule.mapLinearMap (p := ℓ) f.pointMapHom) = ⊤ := by
    refine eq_top_iff.mpr fun g _ ↦ ?_
    rintro - ⟨f, rfl⟩
    rcases not_exists_not.mp (by simpa [hasGeometricCM_iff] using h) f with ⟨n, rfl⟩
    beta_reduce
    rw [mapLinearMap_pointMapHom_intCast]
    exact (Int.cast_commute n g).eq
  rw [tateModuleGeometricEndCentralizer, hS, Submonoid.units_top]

/-- **Without potential complex multiplication, the `ℓ`-adic representation is maximal exactly when
its image contains `SL₂(ℤ_ℓ)`**, that is, every automorphism of the Tate module of determinant
`1`. -/
lemma isMaximalTateModuleGaloisRepresentation_iff_of_not_hasGeometricCM (h : ¬W.HasGeometricCM) :
    W.IsMaximalTateModuleGaloisRepresentation ℓ ↔ (Units.map LinearMap.det).ker ≤
    (W.tateModuleGaloisRepresentation (K := SeparableClosure F) ℓ).asGroupHom.range := by
  rw [IsMaximalTateModuleGaloisRepresentation, W.tateModuleGeometricEndCentralizer_eq_top ℓ h,
    inf_top_eq]

end WeierstrassCurve
