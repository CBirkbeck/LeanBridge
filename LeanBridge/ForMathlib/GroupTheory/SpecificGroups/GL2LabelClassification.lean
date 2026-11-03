import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2ExceptionalConjugacy

/-!
# Sutherland's labels identify the conjugacy classes of subgroups of `GL₂(𝔽_p)`

Every subgroup of `GL₂(𝔽_p)` has exactly one Sutherland label `ℓS.a.b.c[d]`
(`Matrix.GeneralLinearGroup.existsUnique_isCanonicalSutherlandLabel`), and two subgroups have the
same label exactly when they are conjugate
(`Matrix.GeneralLinearGroup.sutherlandLabel_eq_sutherlandLabel_iff`). This is the sense in which
subgroups of `GL₂(𝔽_ℓ)` "are identified using the labels introduced by Sutherland" (LMFDB
`ec.galois_rep_modell_image`; Sutherland, arXiv:1504.07618v7, §6.4).

## Main definitions

* `Matrix.GeneralLinearGroup.sutherlandLabel` (LMFDB `ec.galois_rep_modell_image`): the Sutherland
  label of a subgroup of `GL₂(𝔽_p)`.

## Main results

* `Matrix.GeneralLinearGroup.inf_center_eq_of_index_eq`: for subgroups containing `-1`, the index
  `d` of the determinant and the index `[det K : det Z]` determine the scalars.
* `Matrix.GeneralLinearGroup.inf_center_eq_center_of_S4`: a subgroup with projective image `S₄` and
  surjective determinant contains all the scalars, as Sutherland's label `ℓS4` records.
* `Matrix.GeneralLinearGroup.exists_isSutherlandLabel_of_cls_A4`,
  `Matrix.GeneralLinearGroup.exists_isSutherlandLabel_of_cls_S4`,
  `Matrix.GeneralLinearGroup.exists_isSutherlandLabel_of_cls_A5`: the exceptional subgroups have a
  label.
* `Matrix.GeneralLinearGroup.mem_subgroupConjClass_of_cls_A4`,
  `Matrix.GeneralLinearGroup.mem_subgroupConjClass_of_cls_S4`,
  `Matrix.GeneralLinearGroup.mem_subgroupConjClass_of_cls_A5`: Lemma 3.21 of the paper, the
  invariants determine the conjugacy class of an exceptional subgroup.
* `Matrix.GeneralLinearGroup.IsSutherlandLabel.mem_subgroupConjClass_of_A4`,
  `Matrix.GeneralLinearGroup.IsSutherlandLabel.mem_subgroupConjClass_of_S4`,
  `Matrix.GeneralLinearGroup.IsSutherlandLabel.mem_subgroupConjClass_of_A5`: an exceptional label
  determines the conjugacy class.
* `Matrix.GeneralLinearGroup.exists_isCanonicalSutherlandLabel`,
  `Matrix.GeneralLinearGroup.existsUnique_isCanonicalSutherlandLabel`: **every subgroup of
  `GL₂(𝔽_p)` has exactly one Sutherland label.**
* `Matrix.GeneralLinearGroup.IsCanonicalSutherlandLabel.mem_subgroupConjClass_of_eq`: **two
  subgroups with the same Sutherland label are conjugate.**
* `Matrix.GeneralLinearGroup.sutherlandLabel_eq_iff`: `sutherlandLabel` is the label of
  `IsCanonicalSutherlandLabel`.
* `Matrix.GeneralLinearGroup.sutherlandLabel_eq_sutherlandLabel_iff`: **the label identifies the
  conjugacy classes.**
* `Matrix.GeneralLinearGroup.cls_sutherlandLabel_eq_iff`,
  `Matrix.GeneralLinearGroup.d_sutherlandLabel`: the class and the integer `d` of the label.
* `Matrix.GeneralLinearGroup.cls_sutherlandLabel_eq_G_iff`: the class is `G` exactly for the
  subgroups containing `SL₂(𝔽_p)`.
* `Matrix.GeneralLinearGroup.cls_sutherlandLabel_eq_S4`: with surjective determinant the classes
  `A4` and `A5` do not occur.
-/

open Equiv Matrix MulAction TauCeti

open scoped MatrixGroups Pointwise

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] {H K K' H₁ K₁ : Subgroup (GL (Fin 2) (ZMod p))}
  {L : SutherlandGroupLabel} {ps : List ℕ} {d : ℕ}

lemma detCenterIndex_eq_of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H) :
    detCenterIndex p K = detCenterIndex p H := by
  rw [detCenterIndex, detCenterIndex, inf_center_eq_of_mem_subgroupConjClass hK,
    map_det_eq_of_mem_subgroupConjClass hK]

/-- **The index `d` of the determinant and the index `[det K : det Z]` determine the scalars** of a
subgroup `K` of `GL₂(𝔽_p)` containing `-1`: the determinant of the group of scalars is its group of
squares, which determines it when it contains `-1`. -/
lemma inf_center_eq_of_index_eq (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K)
    (hneg' : (-1 : GL (Fin 2) (ZMod p)) ∈ K') (hd : (K.map det).index = (K'.map det).index)
    (ha : detCenterIndex p K = detCenterIndex p K') :
    K ⊓ Subgroup.center _ = K' ⊓ Subgroup.center _ := by
  have hle {L : Subgroup (GL (Fin 2) (ZMod p))} : (L ⊓ Subgroup.center _).map det ≤ L.map det :=
    Subgroup.map_mono inf_le_left
  have hD₀ : (K ⊓ Subgroup.center _).map det = (K' ⊓ Subgroup.center _).map det := by
    rw [IsCyclic.subgroup_eq_iff_index_eq, ← Subgroup.relIndex_mul_index hle,
      ← Subgroup.relIndex_mul_index hle, hd]
    exact congrArg (· * (K'.map det).index) ha
  have hsub {L L' : Subgroup (GL (Fin 2) (ZMod p))} (hL' : (-1 : GL (Fin 2) (ZMod p)) ∈ L')
      (h : (L ⊓ Subgroup.center _).map det = (L' ⊓ Subgroup.center _).map det) :
      L ⊓ Subgroup.center _ ≤ L' ⊓ Subgroup.center _ := by
    intro x hx
    rcases eq_scalar_of_mem_center (Subgroup.mem_inf.mp hx).2 with ⟨u, rfl⟩
    rcases mem_map_det_inf_center_iff.mp (h ▸ Subgroup.mem_map_of_mem det hx) with ⟨w, hw, hwu⟩
    rw [det_scalar, Fintype.card_fin] at hwu
    exact Subgroup.mem_inf.mpr ⟨scalar_mem_of_sq_eq hL' hw hwu, scalar_mem_center u⟩
  exact le_antisymm (hsub hneg' hD₀) (hsub hneg hD₀.symm)

lemma ne_two_of_mulEquiv {T : Type*} [Group T] (e : projectiveImage K ≃* T) (hT : 6 < Nat.card T) :
    p ≠ 2 := by
  rintro rfl
  have h6 : Nat.card (projectiveImage K) ≤ 6 :=
    (Nat.le_of_dvd Nat.card_pos (K.card_map_dvd ProjGenLinGroup.mk)).trans <|
      K.card_le_card_group.trans_eq <| by
        rw [card_GL_field, Fin.prod_univ_two, ZMod.card]
        rfl
  rw [Nat.card_congr e.toEquiv] at h6
  omega

lemma ne_two_of_A4 (e : projectiveImage K ≃* alternatingGroup (Fin 4)) : p ≠ 2 :=
  ne_two_of_mulEquiv e <| by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide

lemma ne_two_of_S4 (e : projectiveImage K ≃* Perm (Fin 4)) : p ≠ 2 :=
  ne_two_of_mulEquiv e <| by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide

lemma ne_two_of_A5 (e : projectiveImage K ≃* alternatingGroup (Fin 5)) : p ≠ 2 :=
  ne_two_of_mulEquiv e <| by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide

/-- **A subgroup with projective image `S₄` and surjective determinant contains all the scalars**,
as Sutherland's label `ℓS4` records (arXiv:1504.07618v7, §6.4). -/
lemma inf_center_eq_center_of_S4 (hp : p ≠ 2) (f : projectiveImage K ≃* Perm (Fin 4))
    (hd : (K.map det).index = 1) : K ⊓ Subgroup.center _ = Subgroup.center _ := by
  have htop : K.map det = ⊤ := Subgroup.index_eq_one.mp hd
  have hindex : detCenterIndex p K = 2 := by
    rcases detCenterIndex_eq_one_or_two_of_S4 hp f with h | h
    · exfalso
      rw [detCenterIndex, Subgroup.relIndex_eq_one, htop] at h
      rcases quadraticChar_exists_neg_one' (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) with
        ⟨u, hu⟩
      rcases mem_map_det_inf_center_iff.mp (h (Subgroup.mem_top u)) with ⟨w, -, rfl⟩
      rw [Units.val_pow_eq_pow_val, quadraticChar_sq_one' w.ne_zero] at hu
      exact absurd hu (by decide)
    · exact h
  have hD₀ : (K ⊓ Subgroup.center _).map det =
      (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    rw [IsCyclic.subgroup_eq_iff_index_eq, IsCyclic.index_powMonoidHom_range]
    have h₁ : ((K ⊓ Subgroup.center _).map det).index = 2 := by
      rwa [detCenterIndex, htop, Subgroup.relIndex_top_right] at hindex
    rw [h₁]
    have heven : Even (Nat.card (ZMod p)ˣ) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
      exact ((Fact.out : p.Prime).odd_of_ne_two hp).tsub_odd odd_one
    exact (Nat.gcd_eq_right heven.two_dvd).symm
  refine le_antisymm inf_le_right fun x hx ↦ Subgroup.mem_inf.mpr ⟨?_, hx⟩
  rcases eq_scalar_of_mem_center hx with ⟨u, rfl⟩
  have hu : u ^ 2 ∈ (K ⊓ Subgroup.center _).map det := by
    rw [hD₀]
    exact ⟨u, rfl⟩
  rcases mem_map_det_inf_center_iff.mp hu with ⟨w, hw, hwu⟩
  exact scalar_mem_of_sq_eq (neg_one_mem_of_S4 hp f) hw hwu

/-- **A subgroup of class `A4` has a Sutherland label** `ℓA4.a[d]`, `a = [det H : det Z]`. -/
lemma exists_isSutherlandLabel_of_cls_A4 (hS : HasSutherlandClass p H .A4) :
    ∃ L : SutherlandGroupLabel, L.cls = .A4 ∧ IsSutherlandLabel p H L :=
  ⟨⟨.A4, [detCenterIndex p H], _⟩, rfl, hS, rfl, (fun _ hN ↦ nomatch hN), rfl⟩

/-- **A subgroup of class `A5` has a Sutherland label** `ℓA5.1[d]`. -/
lemma exists_isSutherlandLabel_of_cls_A5 (hS : HasSutherlandClass p H .A5) :
    ∃ L : SutherlandGroupLabel, L.cls = .A5 ∧ IsSutherlandLabel p H L := by
  have hH : SutherlandClass.Holds p H .A5 := hS.1
  rcases hH with ⟨K, hK, ⟨f⟩, -⟩
  refine ⟨⟨.A5, [1], _⟩, rfl, hS, rfl, (fun _ hN ↦ nomatch hN), rfl, ?_⟩
  rw [← detCenterIndex_eq_of_mem_subgroupConjClass hK]
  exact detCenterIndex_eq_one_of_A5 (ne_two_of_A5 f) f

/-- **A subgroup of class `S4` has a Sutherland label** `ℓS4`, `ℓS4[d]` or `ℓS4.1[d]`. -/
lemma exists_isSutherlandLabel_of_cls_S4 (hS : HasSutherlandClass p H .S4) :
    ∃ L : SutherlandGroupLabel, L.cls = .S4 ∧ IsSutherlandLabel p H L := by
  have hH : SutherlandClass.Holds p H .S4 := hS.1
  rcases hH with ⟨K, hK, ⟨f⟩, -⟩
  have hp : p ≠ 2 := ne_two_of_S4 f
  rcases detCenterIndex_eq_one_or_two_of_S4 hp f with h | h
  · refine ⟨⟨.S4, [1], _⟩, rfl, hS, rfl, (fun _ hN ↦ nomatch hN), rfl, ?_⟩
    rw [← detCenterIndex_eq_of_mem_subgroupConjClass hK]
    exact h
  · refine ⟨⟨.S4, [], _⟩, rfl, hS, rfl, (fun _ hN ↦ nomatch hN), ?_⟩
    by_cases hd : (H.map det).index = 1
    · refine Or.inl ⟨hd, ?_⟩
      rw [← inf_center_eq_of_mem_subgroupConjClass hK]
      exact inf_center_eq_center_of_S4 hp f (by rwa [map_det_eq_of_mem_subgroupConjClass hK])
    · refine Or.inr ⟨lt_of_le_of_ne (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Ne.symm hd), ?_⟩
      rw [← detCenterIndex_eq_of_mem_subgroupConjClass hK]
      exact h

lemma mem_subgroupConjClass_of_mem_of_mem (hH₁ : H₁ ∈ subgroupConjClass p H)
    (hK₁ : K₁ ∈ subgroupConjClass p K) (h : K₁ ∈ subgroupConjClass p H₁) :
    K ∈ subgroupConjClass p H :=
  orbit_eq_iff.mp <| (orbit_eq_iff.mpr hK₁).symm.trans <|
    (orbit_eq_iff.mpr h).trans (orbit_eq_iff.mpr hH₁)

lemma inf_center_eq_of_mem_of_index_eq (hH₁ : H₁ ∈ subgroupConjClass p H)
    (hK₁ : K₁ ∈ subgroupConjClass p K) (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ H₁)
    (hneg' : (-1 : GL (Fin 2) (ZMod p)) ∈ K₁) (hd : (H.map det).index = (K.map det).index)
    (ha : detCenterIndex p H = detCenterIndex p K) :
    H₁ ⊓ Subgroup.center _ = K₁ ⊓ Subgroup.center _ :=
  inf_center_eq_of_index_eq hneg hneg'
    (by rwa [map_det_eq_of_mem_subgroupConjClass hH₁, map_det_eq_of_mem_subgroupConjClass hK₁])
    (by rwa [detCenterIndex_eq_of_mem_subgroupConjClass hH₁,
      detCenterIndex_eq_of_mem_subgroupConjClass hK₁])

/-- **The invariants of Lemma 3.21 of Sutherland** (arXiv:1504.07618v7): subgroups of `GL₂(𝔽_p)` of
class `A4`, with the same index `d` of the determinant and the same index `[det K : det Z]`, are
conjugate. -/
lemma mem_subgroupConjClass_of_cls_A4 (hH : HasSutherlandClass p H .A4)
    (hK : HasSutherlandClass p K .A4) (hd : (H.map det).index = (K.map det).index)
    (ha : detCenterIndex p H = detCenterIndex p K) : K ∈ subgroupConjClass p H := by
  have hHH : SutherlandClass.Holds p H .A4 := hH.1
  have hHK : SutherlandClass.Holds p K .A4 := hK.1
  rcases hHH with ⟨H₁, hH₁, ⟨e⟩, -⟩
  rcases hHK with ⟨K₁, hK₁, ⟨e'⟩, -⟩
  have hp : p ≠ 2 := ne_two_of_A4 e
  exact mem_subgroupConjClass_of_mem_of_mem hH₁ hK₁ <| mem_subgroupConjClass_of_A4 hp e e'
    (inf_center_eq_of_mem_of_index_eq hH₁ hK₁ (neg_one_mem_of_A4 hp e) (neg_one_mem_of_A4 hp e') hd
      ha) (by rw [detCenterIndex_eq_of_mem_subgroupConjClass hH₁,
        detCenterIndex_eq_of_mem_subgroupConjClass hK₁, ha])

/-- **The invariants of Lemma 3.21 of Sutherland** (arXiv:1504.07618v7): subgroups of `GL₂(𝔽_p)` of
class `S4`, with the same index `d` of the determinant and the same index `[det K : det Z]`, are
conjugate. -/
lemma mem_subgroupConjClass_of_cls_S4 (hH : HasSutherlandClass p H .S4)
    (hK : HasSutherlandClass p K .S4) (hd : (H.map det).index = (K.map det).index)
    (ha : detCenterIndex p H = detCenterIndex p K) : K ∈ subgroupConjClass p H := by
  have hHH : SutherlandClass.Holds p H .S4 := hH.1
  have hHK : SutherlandClass.Holds p K .S4 := hK.1
  rcases hHH with ⟨H₁, hH₁, ⟨e⟩, -⟩
  rcases hHK with ⟨K₁, hK₁, ⟨e'⟩, -⟩
  have hp : p ≠ 2 := ne_two_of_S4 e
  exact mem_subgroupConjClass_of_mem_of_mem hH₁ hK₁ <| mem_subgroupConjClass_of_S4 hp e e'
    (inf_center_eq_of_mem_of_index_eq hH₁ hK₁ (neg_one_mem_of_S4 hp e) (neg_one_mem_of_S4 hp e') hd
      ha) (by rw [detCenterIndex_eq_of_mem_subgroupConjClass hH₁,
        detCenterIndex_eq_of_mem_subgroupConjClass hK₁, ha])

/-- **Lemma 3.21 of Sutherland** (arXiv:1504.07618v7): subgroups of `GL₂(𝔽_p)` of class `A5` with
the same scalars are conjugate. -/
lemma mem_subgroupConjClass_of_cls_A5 (hH : HasSutherlandClass p H .A5)
    (hK : HasSutherlandClass p K .A5) (hZ : H ⊓ Subgroup.center _ = K ⊓ Subgroup.center _) :
    K ∈ subgroupConjClass p H := by
  have hHH : SutherlandClass.Holds p H .A5 := hH.1
  have hHK : SutherlandClass.Holds p K .A5 := hK.1
  rcases hHH with ⟨H₁, hH₁, ⟨e⟩, -⟩
  rcases hHK with ⟨K₁, hK₁, ⟨e'⟩, -⟩
  refine mem_subgroupConjClass_of_mem_of_mem hH₁ hK₁ <|
    mem_subgroupConjClass_of_A5 (ne_two_of_A5 e) e e' ?_
  rwa [inf_center_eq_of_mem_subgroupConjClass hH₁, inf_center_eq_of_mem_subgroupConjClass hK₁]

/-- **Lemma 3.21 of Sutherland** (arXiv:1504.07618v7): two subgroups of `GL₂(𝔽_p)` with the same
label of class `A4` are conjugate. -/
lemma IsSutherlandLabel.mem_subgroupConjClass_of_A4 (hH : IsSutherlandLabel p H ⟨.A4, ps, d⟩)
    (hK : IsSutherlandLabel p K ⟨.A4, ps, d⟩) : K ∈ subgroupConjClass p H := by
  have hPH : SutherlandGroupLabel.ParamsOf p H ⟨.A4, ps, d⟩ := hH.2.2.2
  have hPK : SutherlandGroupLabel.ParamsOf p K ⟨.A4, ps, d⟩ := hK.2.2.2
  rcases ps with _ | ⟨a, _ | ⟨b, ps⟩⟩
  · exact hPH.elim
  · exact mem_subgroupConjClass_of_cls_A4 hH.1 hK.1 (hH.2.1.symm.trans hK.2.1)
      (Eq.trans hPH.symm hPK)
  · exact hPH.elim

/-- **Lemma 3.21 of Sutherland** (arXiv:1504.07618v7): two subgroups of `GL₂(𝔽_p)` with the same
label of class `A5` are conjugate. -/
lemma IsSutherlandLabel.mem_subgroupConjClass_of_A5 (hH : IsSutherlandLabel p H ⟨.A5, ps, d⟩)
    (hK : IsSutherlandLabel p K ⟨.A5, ps, d⟩) : K ∈ subgroupConjClass p H := by
  have hPH : SutherlandGroupLabel.ParamsOf p H ⟨.A5, ps, d⟩ := hH.2.2.2
  have hPK : SutherlandGroupLabel.ParamsOf p K ⟨.A5, ps, d⟩ := hK.2.2.2
  have hHH : SutherlandClass.Holds p H .A5 := hH.1.1
  have hHK : SutherlandClass.Holds p K .A5 := hK.1.1
  rcases hHH with ⟨H₁, hH₁, ⟨e⟩, -⟩
  rcases hHK with ⟨K₁, hK₁, ⟨e'⟩, -⟩
  have hp : p ≠ 2 := ne_two_of_A5 e
  rcases ps with _ | ⟨a, _ | ⟨b, ps⟩⟩
  · exact hPH.elim
  · refine mem_subgroupConjClass_of_cls_A5 hH.1 hK.1 ?_
    rw [← inf_center_eq_of_mem_subgroupConjClass hH₁, ← inf_center_eq_of_mem_subgroupConjClass hK₁]
    exact inf_center_eq_of_mem_of_index_eq hH₁ hK₁ (neg_one_mem_of_A5 hp e)
      (neg_one_mem_of_A5 hp e') (hH.2.1.symm.trans hK.2.1) (hPH.2.trans hPK.2.symm)
  · exact hPH.elim

/-- **Lemma 3.21 of Sutherland** (arXiv:1504.07618v7): two subgroups of `GL₂(𝔽_p)` with the same
label of class `S4` are conjugate. -/
lemma IsSutherlandLabel.mem_subgroupConjClass_of_S4 (hH : IsSutherlandLabel p H ⟨.S4, ps, d⟩)
    (hK : IsSutherlandLabel p K ⟨.S4, ps, d⟩) : K ∈ subgroupConjClass p H := by
  have hPH : SutherlandGroupLabel.ParamsOf p H ⟨.S4, ps, d⟩ := hH.2.2.2
  have hPK : SutherlandGroupLabel.ParamsOf p K ⟨.S4, ps, d⟩ := hK.2.2.2
  have hd : (H.map det).index = (K.map det).index := hH.2.1.symm.trans hK.2.1
  refine mem_subgroupConjClass_of_cls_S4 hH.1 hK.1 hd ?_
  rcases ps with _ | ⟨a, _ | ⟨b, ps⟩⟩
  · rcases hPH with ⟨h₁, hZ⟩ | ⟨h₁, h₂⟩ <;> rcases hPK with ⟨h₁', hZ'⟩ | ⟨h₁', h₂'⟩
    · have hH' : H.map det = ⊤ := Subgroup.index_eq_one.mp (hH.2.1.symm.trans h₁)
      have hK' : K.map det = ⊤ := Subgroup.index_eq_one.mp (hK.2.1.symm.trans h₁)
      rw [detCenterIndex, detCenterIndex, hZ, hZ', hH', hK']
    · exact absurd h₁' (by rw [h₁]; decide)
    · exact absurd h₁ (by rw [h₁']; decide)
    · exact h₂.trans h₂'.symm
  · exact hPH.2.trans hPK.2.symm
  · exact hPH.elim

variable (H) in
/-- **Every subgroup of `GL₂(𝔽_p)` has a Sutherland label** (arXiv:1504.07618v7, §6.4). The class
comes from Dickson's classification (`exists_hasSutherlandClass`), the integers from the lemmas of
Sutherland's section 3. -/
lemma exists_isCanonicalSutherlandLabel :
    ∃ L : SutherlandGroupLabel, IsCanonicalSutherlandLabel p H L := by
  have hne {S : SutherlandClass}
      (h : ∃ L : SutherlandGroupLabel, L.cls = S ∧ IsSutherlandLabel p H L) (hCn : S ≠ .Cn)
      (hNs : S ≠ .Ns) (hNn : S ≠ .Nn) :
      ∃ L : SutherlandGroupLabel, IsCanonicalSutherlandLabel p H L := by
    rcases h with ⟨L, rfl, hL⟩
    exact ⟨L, (isCanonicalSutherlandLabel_iff_of_cls_ne hCn hNs hNn).mpr hL⟩
  rcases exists_hasSutherlandClass H with ⟨S, hS⟩
  cases S
  · exact hne (exists_isSutherlandLabel_of_cls_G hS) nofun nofun nofun
  · exact hne (exists_isSutherlandLabel_of_cls_B hS) nofun nofun nofun
  · exact hne (exists_isSutherlandLabel_of_cls_Cs hS) nofun nofun nofun
  · exact (exists_isCanonicalSutherlandLabel_of_cls_Cn hS).imp fun _ ↦ And.right
  · exact (exists_isCanonicalSutherlandLabel_of_cls_Ns hS).imp fun _ ↦ And.right
  · exact (exists_isCanonicalSutherlandLabel_of_cls_Nn (ne_two_of_hasSutherlandClass_Nn hS)
      hS).imp fun _ ↦ And.right
  · exact hne (exists_isSutherlandLabel_of_cls_A4 hS) nofun nofun nofun
  · exact hne (exists_isSutherlandLabel_of_cls_S4 hS) nofun nofun nofun
  · exact hne (exists_isSutherlandLabel_of_cls_A5 hS) nofun nofun nofun

variable (H) in
/-- **Every subgroup of `GL₂(𝔽_p)` has exactly one Sutherland label** (arXiv:1504.07618v7,
§6.4). -/
lemma existsUnique_isCanonicalSutherlandLabel :
    ∃! L : SutherlandGroupLabel, IsCanonicalSutherlandLabel p H L := by
  rcases exists_isCanonicalSutherlandLabel H with ⟨L, hL⟩
  exact ⟨L, hL, fun _ hL' ↦ hL'.eq hL⟩

lemma IsCanonicalSutherlandLabel.exists_mem_namedSubgroup (hH : IsCanonicalSutherlandLabel p H L)
    (hS : L.cls.toNat < 6) : ∃ N, N ∈ L.namedSubgroup p := by
  rcases L with ⟨S, ps, d⟩
  have h : SutherlandGroupLabel.CanonicalParamsOf p H ⟨S, ps, d⟩ := hH.2.2.2
  cases S <;> simp only at hS <;> first
    | exact absurd hS (by decide)
    | rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, ps⟩⟩⟩⟩ <;> first
        | exact ⟨_, rfl⟩
        | exact h.elim

lemma IsCanonicalSutherlandLabel.isSutherlandLabel (hL : IsCanonicalSutherlandLabel p H L)
    (h : 6 ≤ L.cls.toNat) : IsSutherlandLabel p H L := by
  have hne (S : SutherlandClass) (hS : S.toNat < 6) : L.cls ≠ S :=
    fun hc ↦ absurd (hc ▸ h) hS.not_ge
  exact (isCanonicalSutherlandLabel_iff_of_cls_ne (hne _ (by decide)) (hne _ (by decide))
    (hne _ (by decide))).mp hL

/-- **Two subgroups of `GL₂(𝔽_p)` with the same Sutherland label are conjugate**
(arXiv:1504.07618v7, §6.4): by the label naming a subgroup for the classes `G`, `B`, `Cs`, `Cn`,
`Ns`, `Nn`, and by Lemma 3.21 for the classes `A4`, `S4`, `A5`. -/
lemma IsCanonicalSutherlandLabel.mem_subgroupConjClass_of_eq (hH : IsCanonicalSutherlandLabel p H L)
    (hK : IsCanonicalSutherlandLabel p K L) : K ∈ subgroupConjClass p H := by
  by_cases hS : L.cls.toNat < 6
  · rcases hH.exists_mem_namedSubgroup hS with ⟨N, hN⟩
    exact hH.mem_subgroupConjClass hK hN
  · have hH₁ : IsSutherlandLabel p H L := hH.isSutherlandLabel (not_lt.mp hS)
    have hK₁ : IsSutherlandLabel p K L := hK.isSutherlandLabel (not_lt.mp hS)
    rcases L with ⟨S, ps, d⟩
    cases S <;> simp [SutherlandClass.toNat] at hS
    · exact hH₁.mem_subgroupConjClass_of_A4 hK₁
    · exact hH₁.mem_subgroupConjClass_of_S4 hK₁
    · exact hH₁.mem_subgroupConjClass_of_A5 hK₁

variable (p H) in
/-- **Sutherland's label** `ℓS.a.b.c[d]` of a subgroup of `GL₂(𝔽_p)` (arXiv:1504.07618v7, §6.4;
LMFDB `ec.galois_rep_modell_image`): the unique label of `IsCanonicalSutherlandLabel`, without the
prime. -/
noncomputable def sutherlandLabel : SutherlandGroupLabel :=
  (exists_isCanonicalSutherlandLabel H).choose

variable (p H) in
lemma isCanonicalSutherlandLabel_sutherlandLabel :
    IsCanonicalSutherlandLabel p H (sutherlandLabel p H) :=
  (exists_isCanonicalSutherlandLabel H).choose_spec

/-- **`L` is the Sutherland label of `H` exactly when it satisfies Sutherland's conditions.** -/
lemma sutherlandLabel_eq_iff : sutherlandLabel p H = L ↔ IsCanonicalSutherlandLabel p H L := by
  have h₀ : IsCanonicalSutherlandLabel p H (sutherlandLabel p H) :=
    isCanonicalSutherlandLabel_sutherlandLabel p H
  exact ⟨fun h ↦ h ▸ h₀, h₀.eq⟩

/-- **The Sutherland label identifies the conjugacy classes of subgroups of `GL₂(𝔽_p)`**
(arXiv:1504.07618v7, §6.4; LMFDB `ec.galois_rep_modell_image`, "are identified using the labels"):
two subgroups have the same label exactly when they are conjugate. -/
lemma sutherlandLabel_eq_sutherlandLabel_iff :
    sutherlandLabel p H = sutherlandLabel p K ↔ K ∈ subgroupConjClass p H := by
  have h₀ : IsCanonicalSutherlandLabel p H (sutherlandLabel p H) :=
    isCanonicalSutherlandLabel_sutherlandLabel p H
  refine ⟨fun h ↦ (h ▸ h₀ :
    IsCanonicalSutherlandLabel p H (sutherlandLabel p K)).mem_subgroupConjClass_of_eq
      (isCanonicalSutherlandLabel_sutherlandLabel p K), ?_⟩
  rintro ⟨g, rfl⟩
  exact ((isCanonicalSutherlandLabel_smul_iff _ g).mpr h₀).eq
    (isCanonicalSutherlandLabel_sutherlandLabel p _)

/-- **The class of Sutherland's label** of a subgroup is the class of the subgroup. -/
lemma cls_sutherlandLabel_eq_iff {S : SutherlandClass} :
    (sutherlandLabel p H).cls = S ↔ HasSutherlandClass p H S := by
  have h₀ : HasSutherlandClass p H (sutherlandLabel p H).cls :=
    (isCanonicalSutherlandLabel_sutherlandLabel p H).1
  exact ⟨fun h ↦ h ▸ h₀, h₀.eq⟩

variable (p H) in
/-- **The integer `d` of Sutherland's label** of a subgroup is the index of its determinant. -/
lemma d_sutherlandLabel : (sutherlandLabel p H).d = (H.map det).index :=
  (isCanonicalSutherlandLabel_sutherlandLabel p H).2.1

/-- **The class of the Sutherland label of a subgroup is `G` exactly when it contains `SL₂(𝔽_p)`**
(arXiv:1504.07618v7, §6.4). -/
lemma cls_sutherlandLabel_eq_G_iff : (sutherlandLabel p H).cls = .G ↔ det.ker ≤ H :=
  ⟨fun h ↦ det_ker_le_of_holds_G (cls_sutherlandLabel_eq_iff.mp h).1, fun h ↦ by_contra fun hne ↦
    (isCanonicalSutherlandLabel_sutherlandLabel p H).1.2 .G
      (Nat.pos_of_ne_zero fun h₀ ↦ hne (SutherlandClass.toNat_injective h₀))
      ⟨H, mem_orbit_self H, h⟩⟩

/-- **A subgroup of `GL₂(𝔽_p)` with surjective determinant has no label of class `A4` or `A5`**
(LMFDB `ec.galois_rep_modell_image`): an exceptional class is then `S4`. -/
lemma cls_sutherlandLabel_eq_S4 (hdet : H.map det = ⊤) (h : 6 ≤ (sutherlandLabel p H).cls.toNat) :
    (sutherlandLabel p H).cls = .S4 :=
  ((isCanonicalSutherlandLabel_sutherlandLabel p H).isSutherlandLabel h).cls_eq_S4 hdet h

end Matrix.GeneralLinearGroup
