import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Basic

/-!
# The dual of a cyclic isogeny

Over a field of characteristic zero, the dual `φ̂` of a cyclic isogeny `φ : W₁ → W₂` of degree `n`
is cyclic. Over an algebraic closure, `φ` is onto on points and `φ̂ ∘ φ = [n]`, so the kernel of
`φ̂` is the image under `φ` of the `n`-torsion `W₁[n]`, isomorphic to the quotient of `W₁[n]` by
the kernel of `φ`. Now `W₁[n] ≅ (ℤ/n)²`, and the quotient of `(ℤ/n)²` by a cyclic subgroup of
order `n` is cyclic.

## Main results

* `TauCeti.Isogeny.IsCyclic.dual`: over a field of characteristic zero, the dual of a cyclic isogeny
  is cyclic.
-/

open AddSubgroup (torsionBy)
open TauCeti

variable {n : ℕ} [NeZero n]

private lemma exists_sub_eq_one_of_addOrderOf_eq {v : ZMod n × ZMod n} (hv : addOrderOf v = n) :
    ∃ x y : ZMod n, v.2 * x - v.1 * y = 1 := by
  have hg : (v.1.val.gcd v.2.val).Coprime n := by
    have hgn : (v.1.val.gcd v.2.val).gcd n ∣ n := Nat.gcd_dvd_right _ _
    have key : ∀ c : ℕ, (v.1.val.gcd v.2.val).gcd n ∣ c → (n / (v.1.val.gcd v.2.val).gcd n) •
        (c : ZMod n) = 0 := by
      rintro c ⟨k, rfl⟩
      rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact ⟨k, by rw [← mul_assoc, Nat.div_mul_cancel hgn]⟩
    have h0 : (n / (v.1.val.gcd v.2.val).gcd n) • v = 0 := Prod.ext
      (by simpa using key _ ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)))
      (by simpa using key _ ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)))
    have hdvd : addOrderOf v ∣ n / (v.1.val.gcd v.2.val).gcd n := addOrderOf_dvd_of_nsmul_eq_zero h0
    rw [hv] at hdvd
    have hng : n / (v.1.val.gcd v.2.val).gcd n = n :=
      le_antisymm (Nat.div_le_self _ _) (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (NeZero.pos n)
        hgn) (Nat.pos_of_dvd_of_pos hgn (NeZero.pos n))) hdvd)
    exact (Nat.div_div_self hgn (NeZero.ne n)).symm.trans (by rw [hng, Nat.div_self (NeZero.pos n)])
  have hbez : (v.1.val.gcd v.2.val : ZMod n) = v.1 * v.1.val.gcdA v.2.val +
      v.2 * v.1.val.gcdB v.2.val := by
    simpa using congrArg (Int.cast : ℤ → ZMod n) (v.1.val.gcd_eq_gcd_ab v.2.val)
  refine ⟨(v.1.val.gcd v.2.val : ZMod n)⁻¹ * v.1.val.gcdB v.2.val,
    -((v.1.val.gcd v.2.val : ZMod n)⁻¹ * v.1.val.gcdA v.2.val), ?_⟩
  linear_combination ZMod.coe_mul_inv_eq_one _ hg - (v.1.val.gcd v.2.val : ZMod n)⁻¹ * hbez

private lemma isAddCyclic_quotient_of_card_eq (C : AddSubgroup (ZMod n × ZMod n)) [IsAddCyclic C]
    (hC : Nat.card C = n) : IsAddCyclic ((ZMod n × ZMod n) ⧸ C) := by
  rcases IsAddCyclic.exists_generator (α := C) with ⟨g, hg⟩
  have hv : addOrderOf g.1 = n := by
    rw [AddSubgroup.addOrderOf_coe, addOrderOf_eq_card_of_forall_mem_zmultiples hg, hC]
  rcases exists_sub_eq_one_of_addOrderOf_eq hv with ⟨x, y, hxy⟩
  let f : ZMod n × ZMod n →+ ZMod n :=
    (AddMonoidHom.mulLeft g.1.2).comp (.fst _ _) - (AddMonoidHom.mulLeft g.1.1).comp (.snd _ _)
  have hfp : ∀ p : ZMod n × ZMod n, f p = g.1.2 * p.1 - g.1.1 * p.2 := fun _ ↦ rfl
  have hf : Function.Surjective f := fun z ↦ ⟨(z * x, z * y), by
    rw [hfp]
    linear_combination z * hxy⟩
  have hker : C = f.ker := by
    refine AddSubgroup.eq_of_le_of_card_ge (fun c hc ↦ ?_) ?_
    · rcases hg ⟨c, hc⟩ with ⟨k, hk⟩
      have hc' : k • g.1 = c := congrArg Subtype.val hk
      rw [AddMonoidHom.mem_ker, ← hc', map_zsmul, hfp, mul_comm, sub_self, smul_zero]
    · have h : Nat.card (ZMod n × ZMod n) = Nat.card ((ZMod n × ZMod n) ⧸ f.ker) * Nat.card f.ker :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
        Nat.card_prod, Nat.card_zmod] at h
      rw [hC]
      exact (Nat.eq_of_mul_eq_mul_left (NeZero.pos n) h).ge
  exact ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)).isAddCyclic.mpr inferInstance

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] [CharZero K] {W₁ W₂ : WeierstrassCurve.Affine K} [W₁.IsElliptic]
  [W₂.IsElliptic] {φ : Isogeny W₁ W₂}

/-- **The dual of a cyclic isogeny is cyclic**, over a field of characteristic zero: the kernel of
`φ̂` is the image under `φ` of the `n`-torsion, isomorphic to the quotient of `(ℤ/n)²` by the kernel
of `φ`, a cyclic subgroup of order `n = deg φ`, and such a quotient is cyclic. -/
lemma IsCyclic.dual (hφ : φ.IsCyclic) : φ.dual.IsCyclic := by
  classical
  have hB : φ.dual.geometricKer =
      (Hom.ofIsogeny (φ.map (algebraMap K (AlgebraicClosure K))).dual).pointMapHom.ker := by
    rw [geometricKer, dual_map]
  have hBA : ∀ P, (Hom.ofIsogeny (φ.map (algebraMap K (AlgebraicClosure K))).dual).pointMapHom
      ((Hom.ofIsogeny (φ.map (algebraMap K (AlgebraicClosure K)))).pointMapHom P) =
      φ.degree • P := fun P ↦ by
    rw [Hom.pointMapHom_apply, Hom.pointMapHom_apply, pointMap_dual_pointMap, degree_map]
  have hA :
      Function.Surjective (Hom.ofIsogeny (φ.map (algebraMap K (AlgebraicClosure K)))).pointMapHom :=
    Hom.pointMap_surjective (Hom.ofIsogeny_ne_zero _)
  have : NeZero φ.degree := ⟨φ.degree_ne_zero⟩
  rcases (W₁.map (algebraMap K (AlgebraicClosure K))).torsion_addEquiv_prod φ.degree
    (Nat.cast_ne_zero.mpr φ.degree_ne_zero) with ⟨e⟩
  have hle : φ.geometricKer ≤ torsionBy _ (φ.degree : ℤ) := fun P hP ↦ by
    have h : Nat.card φ.geometricKer • (⟨P, hP⟩ : φ.geometricKer) = 0 := card_nsmul_eq_zero'
    rw [card_geometricKer] at h
    exact torsionBy.nsmul_iff.mpr <| congrArg Subtype.val h
  let C : AddSubgroup (ZMod φ.degree × ZMod φ.degree) :=
    (φ.geometricKer.addSubgroupOf (torsionBy _ (φ.degree : ℤ))).map e.toAddMonoidHom
  let eC : C ≃+ φ.geometricKer :=
    (e.addSubgroupMap _).symm.trans (AddSubgroup.addSubgroupOfEquivOfLe hle)
  have : IsAddCyclic C := eC.isAddCyclic.mpr hφ
  have : IsAddCyclic ((ZMod φ.degree × ZMod φ.degree) ⧸ C) :=
    isAddCyclic_quotient_of_card_eq C <| (Nat.card_congr eC.toEquiv).trans φ.card_geometricKer
  let A' : torsionBy (W₁.map (algebraMap K (AlgebraicClosure K))).Point (φ.degree : ℤ) →+
      φ.dual.geometricKer :=
    ((Hom.ofIsogeny (φ.map (algebraMap K (AlgebraicClosure K)))).pointMapHom.domRestrict
      (torsionBy _ (φ.degree : ℤ))).codRestrict φ.dual.geometricKer fun P ↦ by
        rw [hB, AddMonoidHom.mem_ker, AddMonoidHom.domRestrict_apply, hBA]
        exact torsionBy.nsmul_iff.mp P.2
  have hA' : Function.Surjective A' := fun Q ↦ by
    rcases hA Q with ⟨P, hP⟩
    refine ⟨⟨P, torsionBy.nsmul_iff.mpr ?_⟩, Subtype.ext hP⟩
    rw [← hBA, hP, ← AddMonoidHom.mem_ker, ← hB]
    exact Q.2
  let h₀ : ZMod φ.degree × ZMod φ.degree →+ φ.dual.geometricKer := A'.comp e.symm.toAddMonoidHom
  have hC : C ≤ h₀.ker := by
    rintro _ ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf, geometricKer, AddMonoidHom.mem_ker] at ht
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
    exact Subtype.ext ht
  rw [IsCyclic]
  exact isAddCyclic_of_surjective (QuotientAddGroup.lift C h₀ hC) fun Q ↦
    (hA'.comp e.symm.surjective Q).elim fun x hx ↦ ⟨(x : (ZMod φ.degree × ZMod φ.degree) ⧸ C), hx⟩

end TauCeti.Isogeny
