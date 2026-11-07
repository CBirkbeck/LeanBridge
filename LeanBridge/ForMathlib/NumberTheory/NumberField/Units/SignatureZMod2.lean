import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.SignatureRank
import TauCeti.Algebra.Order.Ring.Units

/-!
# Signatures of elements of a number field in `𝔽₂`

The LMFDB (`nf.unit_signature_rank`) defines the signature of a nonzero element `α` of a number
field `K` as the vector `(sign(σ_1(α)), …, sign(σ_{r₁}(α))) ∈ 𝔽₂ ^ r₁` over the real embeddings
`σ_i` of `K`, where `sign(x)` is `0` for `x > 0` and `1` for `x < 0`, and the unit signature rank as
the dimension over `𝔽₂` of the space of signatures of the units of `𝓞 K`.
`NumberField.unitSignatureRank` is defined from Tau Ceti's signatures, valued in the sign group
`ℝˣ ⧸ ℝˣ₊` at each real place. This file defines the signature in `𝔽₂` as the LMFDB does, shows that
the signatures of the units form a subspace of `𝔽₂ ^ r₁`, and proves that its dimension is
`NumberField.unitSignatureRank`.

## Main definitions

* `NumberField.elementSignature` (LMFDB `nf.unit_signature_rank`): the signature of a nonzero
  element of `K` in `𝔽₂ ^ r₁`, additive in the element.
* `NumberField.unitSignatureSpace` (LMFDB `nf.unit_signature_rank`): the subspace of `𝔽₂ ^ r₁` of
  the signatures of the units of `𝓞 K`.

## Main results

* `NumberField.unitSignatureRank_eq_finrank` (LMFDB `nf.unit_signature_rank`): the unit signature
  rank is the dimension over `𝔽₂` of the space of signatures of units.
-/

open TauCeti GlobalNumberFields NumberField InfinitePlace Module

namespace NumberField

variable {K : Type*} [Field K]

private lemma ite_pos_mul_eq_add {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (if 0 < a * b then 0 else 1 : ZMod 2) = (if 0 < a then 0 else 1) + if 0 < b then 0 else 1 := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · simp [mul_pos_of_neg_of_neg ha hb, ha.not_gt, hb.not_gt]
    decide
  · simp [hb]
  · simp [ha]
  · simp [hb]

/-- The **signature** (LMFDB `nf.unit_signature_rank`) of a nonzero element `α` of `K`: the vector,
indexed by the real places `w` of `K`, of the signs `sign(σ_w(α)) ∈ 𝔽₂` at the real embeddings
`σ_w`, where `sign(x)` is `0` for `x > 0` and `1` for `x < 0`. It is additive in `α`, the product
of two elements having the sum of their signatures. -/
noncomputable def elementSignature :
    Additive Kˣ →+ ({w : InfinitePlace K // w.IsReal} → ZMod 2) where
  toFun α w := if 0 < embedding_of_isReal w.2 (α.toMul : K) then 0 else 1
  map_zero' := by
    ext w
    simp
  map_add' α β := by
    ext w
    simp only [toMul_add, Units.val_mul, map_mul]
    exact ite_pos_mul_eq_add ((map_ne_zero _).mpr α.toMul.ne_zero)
      ((map_ne_zero _).mpr β.toMul.ne_zero)

lemma elementSignature_apply (α : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    elementSignature (Additive.ofMul α) w = if 0 < embedding_of_isReal w.2 (α : K) then 0 else 1 :=
  rfl

variable (K) in
/-- The **space of signatures of units** (LMFDB `nf.unit_signature_rank`): the signatures in
`𝔽₂ ^ r₁` of the units of `𝓞 K`, which form a subspace since the signature is additive. -/
noncomputable def unitSignatureSpace :
    Submodule (ZMod 2) ({w : InfinitePlace K // w.IsReal} → ZMod 2) :=
  AddSubgroup.toZModSubmodule 2
    (elementSignature.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom).toAdditive).range

private lemma injective_signEquiv_comp :
    Function.Injective fun (s : {w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) w ↦
      if Units.signEquiv ℝ (s w) = 1 then (0 : ZMod 2) else 1 := by
  intro s t hst
  funext w
  have hw : (if Units.signEquiv ℝ (s w) = 1 then (0 : ZMod 2) else 1) =
      if Units.signEquiv ℝ (t w) = 1 then 0 else 1 := congrFun hst w
  refine (Units.signEquiv ℝ).injective ?_
  rcases Int.units_eq_one_or (Units.signEquiv ℝ (s w)) with hs | hs <;>
    rcases Int.units_eq_one_or (Units.signEquiv ℝ (t w)) with ht | ht <;>
    simp [hs, ht] at hw ⊢

private lemma ite_signEquiv_unitSignature (u : (𝓞 K)ˣ) :
    (fun w ↦ if Units.signEquiv ℝ (unitSignature u w) = 1 then (0 : ZMod 2) else 1) =
      elementSignature (Additive.ofMul (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)) :=
  funext fun _ ↦ if_congr (Units.signEquiv_mk_eq_one_iff _) rfl rfl

lemma coe_unitSignatureSpace :
    (unitSignatureSpace K : Set ({w : InfinitePlace K // w.IsReal} → ZMod 2)) =
      (fun (s : {w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) w ↦
        if Units.signEquiv ℝ (s w) = 1 then (0 : ZMod 2) else 1) ''
        (integerUnitSignatures (K := K) : Set _) := by
  ext x
  simp only [unitSignatureSpace]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨unitSignature u.toMul, ⟨u.toMul, rfl⟩, ite_signEquiv_unitSignature u.toMul⟩
  · rintro ⟨-, ⟨u, rfl⟩, rfl⟩
    exact ⟨Additive.ofMul u, (ite_signEquiv_unitSignature u).symm⟩

variable [NumberField K]

/-- **The unit signature rank is the dimension of the space of signatures of units**
(LMFDB `nf.unit_signature_rank`): `NumberField.unitSignatureRank K` is the dimension over `𝔽₂` of
the subspace of `𝔽₂ ^ r₁` formed by the signatures of the units of `𝓞 K`. -/
lemma unitSignatureRank_eq_finrank :
    unitSignatureRank K = finrank (ZMod 2) (unitSignatureSpace K) := by
  have hcard : Nat.card (integerUnitSignatures (K := K)) = Nat.card (unitSignatureSpace K) := by
    rw [← SetLike.coe_sort_coe (unitSignatureSpace K), coe_unitSignatureSpace,
      Nat.card_image_of_injective injective_signEquiv_comp]
    rfl
  rw [← (Nat.pow_right_injective le_rfl).eq_iff, two_pow_unitSignatureRank, hcard,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

end NumberField
