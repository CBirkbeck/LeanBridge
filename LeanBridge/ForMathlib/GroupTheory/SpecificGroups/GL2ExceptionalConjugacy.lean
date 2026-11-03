import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2ExceptionalLifts

/-!
# Exceptional subgroups of `GL₂(𝔽_p)` are determined by their invariants

A subgroup `K` of `GL₂(𝔽_p)` with projective image `A₄`, `S₄` or `A₅` is determined up to conjugacy
by the type of its projective image, its group of scalars `Z = K ∩ Z(p)`, and the index
`[det K : det Z]` (Lemma 3.21 of Sutherland, arXiv:1504.07618v7, who deduces it from the
classification of Flannery and O'Brien, *Linear groups of small degree over finite fields*,
Internat. J. Algebra Comput. 15 (2005)). The proof here is direct. Choose lifts to `K` of a
generating pair `(s, t)` of the image with `s` of order `2`, `t` of order `3` and `s t` of order
`3`, `4` or `5`. The traces and determinants of the lifts `S`, `X`, `S X` are related by the orders,
and the lifts can be scaled by `Z`, so they are determined by the invariants, in some cases after
replacing `(s, t)` by another generating pair; and pairs of matrices with the same traces and
determinants are conjugate (`Matrix.exists_mul_eq_mul_of_trace_det_eq`).

## Main results

* `Matrix.GeneralLinearGroup.mem_subgroupConjClass_of_A5`,
  `Matrix.GeneralLinearGroup.mem_subgroupConjClass_of_A4`,
  `Matrix.GeneralLinearGroup.mem_subgroupConjClass_of_S4`: Lemma 3.21 of Sutherland, for the
  projective images `A₅`, `A₄` and `S₄`.
* `Matrix.GeneralLinearGroup.detCenterIndex_eq_one_of_A5`: the index `[det K : det Z]` is `1` for a
  projective image `A₅`.
* `Matrix.GeneralLinearGroup.detCenterIndex_eq_one_or_two_of_S4`: it is `1` or `2` for a projective
  image `S₄`.
-/

open Equiv Matrix MulAction TauCeti

open scoped MatrixGroups Pointwise

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] {K K' : Subgroup (GL (Fin 2) (ZMod p))} {T T' : Type*} [Group T]
  [Group T'] (e : projectiveImage K ≃* T) (e' : projectiveImage K' ≃* T') {s t : T} {s' t' : T'}
  {S X S' X' Y : GL (Fin 2) (ZMod p)} {u v w z : (ZMod p)ˣ}

lemma val_neg_of_field : (-Y).val = -Y.val :=
  Units.val_neg Y

lemma trace_val_neg : (-Y).val.trace = -Y.val.trace := by
  rw [val_neg_of_field, trace_neg]

lemma det_val_neg : (-Y).val.det = Y.val.det := by
  rw [val_neg_of_field, Matrix.det_neg]
  simp

lemma trace_val_neg_mul (A : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    ((-Y).val * A).trace = -(Y.val * A).trace := by
  rw [val_neg_of_field, Matrix.neg_mul, trace_neg]

variable (v) in
lemma val_scalar_eq_smul : (scalar (Fin 2) v).val = (v : ZMod p) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable (Y v) in
lemma val_mul_scalar : (Y * scalar (Fin 2) v).val = (v : ZMod p) • Y.val := by
  rw [Units.val_mul, val_scalar_eq_smul, Matrix.mul_smul, Matrix.mul_one]

lemma neg_eq_mul_scalar : -Y = Y * scalar (Fin 2) (-1) := Units.ext <| by
  rw [val_neg_of_field, val_mul_scalar, Units.val_neg, Units.val_one, neg_one_smul]

lemma mk_neg : ProjGenLinGroup.mk (-Y) = ProjGenLinGroup.mk Y := by
  rw [neg_eq_mul_scalar, map_mul, ProjGenLinGroup.mk_scalar, mul_one]

lemma neg_mem_of_neg_one_mem (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K) (hY : Y ∈ K) : -Y ∈ K := by
  simpa using mul_mem hneg hY

lemma det_eq_one_of_val_det (h : Y.val.det = 1) : det Y = 1 :=
  Units.ext <| by rw [val_det_apply, h, Units.val_one]

lemma val_det_eq_one_of_det (h : det Y = 1) : Y.val.det = 1 := by
  rw [← val_det_apply, h, Units.val_one]

lemma scalar_mem_iff_of_inf_center_eq (hZ : K ⊓ Subgroup.center _ = K' ⊓ Subgroup.center _) :
    scalar (Fin 2) w ∈ K ↔ scalar (Fin 2) w ∈ K' :=
  ⟨fun h ↦ (Subgroup.mem_inf.mp (hZ ▸ Subgroup.mem_inf.mpr ⟨h, scalar_mem_center w⟩ :
    scalar (Fin 2) w ∈ K' ⊓ Subgroup.center _)).1, fun h ↦ (Subgroup.mem_inf.mp
      (hZ.symm ▸ Subgroup.mem_inf.mpr ⟨h, scalar_mem_center w⟩ :
        scalar (Fin 2) w ∈ K ⊓ Subgroup.center _)).1⟩

lemma scalar_mem_of_sq_eq (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K) (hw : scalar (Fin 2) w ∈ K)
    (h : w ^ 2 = u ^ 2) : scalar (Fin 2) u ∈ K := by
  have h₁ : (w : ZMod p) * w = u * u := by
    rw [← Units.val_mul, ← Units.val_mul, ← sq, ← sq, h]
  rcases mul_self_eq_mul_self_iff.mp h₁ with h₂ | h₂
  · rwa [← Units.ext h₂]
  · have h₃ : scalar (Fin 2) u = -scalar (Fin 2) w := Units.ext <| by
      rw [val_neg_of_field, val_scalar_eq_smul, val_scalar_eq_smul, ← neg_smul, h₂, neg_neg]
    rw [h₃]
    exact neg_mem_of_neg_one_mem hneg hw

lemma mem_map_det_inf_center_iff :
    v ∈ (K ⊓ Subgroup.center _).map det ↔ ∃ w : (ZMod p)ˣ, scalar (Fin 2) w ∈ K ∧ w ^ 2 = v := by
  refine ⟨?_, fun ⟨w, hw, hwv⟩ ↦ ⟨scalar (Fin 2) w, Subgroup.mem_inf.mpr ⟨hw, scalar_mem_center w⟩,
    by rw [det_scalar, Fintype.card_fin, hwv]⟩⟩
  rintro ⟨z, hz, rfl⟩
  rcases Subgroup.mem_inf.mp hz with ⟨hzK, hzc⟩
  rcases eq_scalar_of_mem_center hzc with ⟨w, rfl⟩
  exact ⟨w, hzK, by rw [det_scalar, Fintype.card_fin]⟩

lemma det_commutator_of_trace_eq_zero {A B : Matrix (Fin 2) (Fin 2) (ZMod p)} (hA : A.trace = 0) :
    (A * B - B * A).det = 4 * A.det * B.det - B.trace * B.trace * A.det -
      (A * B).trace * (A * B).trace := by
  rw [trace_fin_two] at hA
  have h₁₁ : A 1 1 = -A 0 0 := by
    linear_combination hA
  simp only [det_fin_two, trace_fin_two, sub_apply, mul_apply, Fin.sum_univ_two, h₁₁]
  ring1

private lemma detCenterIndex_eq_one_of_lifts (hgen : Subgroup.closure ({s, t} : Set T) = ⊤)
    (hSK : S ∈ K) (hXK : X ∈ K) (hmS : ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p)))
    (hmX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p)))
    (hdS : det S ∈ (K ⊓ Subgroup.center _).map det)
    (hdX : det X ∈ (K ⊓ Subgroup.center _).map det) : detCenterIndex p K = 1 := by
  rw [detCenterIndex, Subgroup.relIndex_eq_one, Subgroup.map_le_iff_le_comap]
  exact le_of_lifts_mem e hgen (fun z hz ↦ Subgroup.mem_map_of_mem _ hz) hSK hXK hdS hdX hmS hmX

lemma exists_lift_trace_eq_one (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K)
    (ht : ∃ a b : T, a * b * a⁻¹ * b⁻¹ = t) (ht₃ : t ^ 3 = 1) (ht₁ : t ≠ 1) :
    ∃ X ∈ K, ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p)) ∧ X.val.trace = 1 ∧
      X.val.det = 1 := by
  rcases exists_lift_det_eq_one e ht with ⟨X₀, hX₀, hmX₀, hdX₀⟩
  have h₁ : X₀.val.trace * X₀.val.trace = X₀.val.det :=
    trace_mul_self_eq_det_of_pow_three_mem_center (notMem_center_of_lift e hmX₀ ht₁)
      (pow_mem_center_of_lift e hmX₀ ht₃)
  rw [val_det_eq_one_of_det hdX₀] at h₁
  rcases mul_self_eq_one_iff.mp h₁ with h₂ | h₂
  · exact ⟨X₀, hX₀, hmX₀, h₂, val_det_eq_one_of_det hdX₀⟩
  · exact ⟨-X₀, neg_mem_of_neg_one_mem hneg hX₀, by rw [mk_neg, hmX₀], by
      rw [trace_val_neg, h₂, neg_neg], by rw [det_val_neg, val_det_eq_one_of_det hdX₀]⟩

lemma exists_lifts_of_order_five (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K)
    (hs : ∃ a b : T, a * b * a⁻¹ * b⁻¹ = s) (ht : ∃ a b : T, a * b * a⁻¹ * b⁻¹ = t)
    (hs₂ : s ^ 2 = 1) (hs₁ : s ≠ 1) (ht₃ : t ^ 3 = 1) (ht₁ : t ≠ 1) (hu₅ : (s * t) ^ 5 = 1)
    (hu₁ : s * t ≠ 1) : ∃ S ∈ K, ∃ X ∈ K, ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p)) ∧
      ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p)) ∧ S.val.trace = 0 ∧ S.val.det = 1 ∧
        X.val.trace = 1 ∧ X.val.det = 1 ∧ (S.val * X.val).trace * (S.val * X.val).trace =
          (S.val * X.val).trace + 1 := by
  rcases exists_lift_det_eq_one e hs with ⟨S₀, hS₀, hmS₀, hdS₀⟩
  have hval : S₀.val.det = 1 := val_det_eq_one_of_det hdS₀
  have htrS : S₀.val.trace = 0 := trace_eq_zero_of_sq_mem_center
    (notMem_center_of_lift e hmS₀ hs₁) (pow_mem_center_of_lift e hmS₀ hs₂)
  rcases exists_lift_trace_eq_one e hneg ht ht₃ ht₁ with ⟨X, hXK, hmX, htrX, hdX⟩
  have hmU : ProjGenLinGroup.mk (S₀ * X) = (e.symm (s * t) : PGL(Fin 2, ZMod p)) :=
    mk_mul_of_lift e hmS₀ hmX
  have hq : (S₀ * X).val.trace ^ 4 - 3 * (S₀ * X).val.trace ^ 2 * (S₀ * X).val.det +
      (S₀ * X).val.det ^ 2 = 0 := quartic_of_pow_five_mem_center (notMem_center_of_lift e hmU hu₁)
    (pow_mem_center_of_lift e hmU hu₅)
  rw [Units.val_mul, Matrix.det_mul, hval, hdX, mul_one] at hq
  rcases mul_eq_zero.mp (by linear_combination hq :
    ((S₀.val * X.val).trace * (S₀.val * X.val).trace - (S₀.val * X.val).trace - 1) *
      ((S₀.val * X.val).trace * (S₀.val * X.val).trace + (S₀.val * X.val).trace - 1) = 0) with
    h | h
  · exact ⟨S₀, hS₀, X, hXK, hmS₀, hmX, htrS, hval, htrX, hdX, by linear_combination h⟩
  · refine ⟨-S₀, neg_mem_of_neg_one_mem hneg hS₀, X, hXK, by rw [mk_neg, hmS₀], hmX, by
      rw [trace_val_neg, htrS, neg_zero], by rw [det_val_neg, hval], htrX, hdX, ?_⟩
    rw [trace_val_neg_mul]
    linear_combination h

/-- The element `(0 1)(2 3)` of `A₅`. -/
private def a5s : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- The element `(0 2)(1 3)` of `A₅`. -/
private def a5v : alternatingGroup (Fin 5) :=
  ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- A `3`-cycle of `A₅`, with `a5s * a5t` a `5`-cycle. -/
private def a5t : alternatingGroup (Fin 5) :=
  ⟨swap 1 2 * swap 2 4, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- The conjugate of `a5t` by the transposition `(0 1)`. -/
private def a5t₁ : alternatingGroup (Fin 5) :=
  ⟨swap 0 2 * swap 2 4, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- The element of `A₅` with `a5s * a5t₁ = a5y * (a5s * a5t) ^ 2 * a5y⁻¹`. -/
private def a5y : alternatingGroup (Fin 5) :=
  ⟨swap 1 4 * swap 4 2, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- An element of `A₅` used to write `a5s`, `a5t`, `a5t₁` as commutators. -/
private def a5c₁ : alternatingGroup (Fin 5) :=
  ⟨swap 1 2 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- An element of `A₅` used to write `a5s`, `a5t`, `a5t₁` as commutators. -/
private def a5c₂ : alternatingGroup (Fin 5) :=
  ⟨swap 0 2 * swap 2 1, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- An element of `A₅` used to write `a5s`, `a5t`, `a5t₁` as commutators. -/
private def a5c₃ : alternatingGroup (Fin 5) :=
  ⟨swap 2 4 * swap 4 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- An element of `A₅` used to write `a5s`, `a5t`, `a5t₁` as commutators. -/
private def a5c₄ : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩

private lemma closure_eq_top_of_orders {x y : alternatingGroup (Fin 5)} (hx : orderOf x = 2)
    (hy : orderOf y = 3) (hxy : orderOf (x * y) = 5) :
    Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  have hxm : x ∈ Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5))) :=
    Subgroup.subset_closure (by simp)
  have hym : y ∈ Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5))) :=
    Subgroup.subset_closure (by simp)
  have hd₂ : orderOf x ∣ Nat.card (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))) :=
    Subgroup.orderOf_dvd_natCard _ hxm
  have hd₃ : orderOf y ∣ Nat.card (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))) :=
    Subgroup.orderOf_dvd_natCard _ hym
  have hd₅ : orderOf (x * y) ∣
      Nat.card (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))) :=
    Subgroup.orderOf_dvd_natCard _ (mul_mem hxm hym)
  rw [hx] at hd₂
  rw [hy] at hd₃
  rw [hxy] at hd₅
  have hcard : Nat.card (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))) *
      (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))).index = 60 := by
    rw [Subgroup.card_mul_index, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have h30 : 30 ∣ Nat.card (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))) :=
    (by norm_num : Nat.Coprime 6 5).mul_dvd_of_dvd_of_dvd
      ((by norm_num : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd hd₂ hd₃) hd₅
  rcases h30 with ⟨k, hk⟩
  rw [hk] at hcard
  have hi : (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))).index = 1 ∨
      (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))).index = 2 := by
    have h₁ : k * (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))).index = 2 := by
      nlinarith
    exact (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro_left k h₁)
  rcases hi with hi | hi
  · exact Subgroup.index_eq_one.mp hi
  · have hnormal : (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))).Normal :=
      Subgroup.normal_of_index_eq_two hi
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.closure ({x, y} : Set (alternatingGroup (Fin 5)))) with hbot | htop
    · rw [hbot] at hxm
      have h₁ : x = 1 := Subgroup.mem_bot.mp hxm
      rw [h₁, orderOf_one] at hx
      omega
    · exact htop

private lemma closure_a5s_a5t :
    Subgroup.closure ({a5s, a5t} : Set (alternatingGroup (Fin 5))) = ⊤ :=
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  closure_eq_top_of_orders (orderOf_eq_prime (by decide) (by decide))
    (orderOf_eq_prime (by decide) (by decide)) (orderOf_eq_prime (by decide) (by decide))

private lemma closure_a5s_a5t₁ :
    Subgroup.closure ({a5s, a5t₁} : Set (alternatingGroup (Fin 5))) = ⊤ :=
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  closure_eq_top_of_orders (orderOf_eq_prime (by decide) (by decide))
    (orderOf_eq_prime (by decide) (by decide)) (orderOf_eq_prime (by decide) (by decide))

lemma neg_one_mem_of_A5 (hp : p ≠ 2) (f : projectiveImage K ≃* alternatingGroup (Fin 5)) :
    (-1 : GL (Fin 2) (ZMod p)) ∈ K :=
  neg_one_mem_of_lifts f hp (s₁ := a5s) (s₂ := a5v) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

private lemma exists_lifts_a5s_a5t (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K)
    (f : projectiveImage K ≃* alternatingGroup (Fin 5)) :
    ∃ S ∈ K, ∃ X ∈ K, ProjGenLinGroup.mk S = (f.symm a5s : PGL(Fin 2, ZMod p)) ∧
      ProjGenLinGroup.mk X = (f.symm a5t : PGL(Fin 2, ZMod p)) ∧ S.val.trace = 0 ∧ S.val.det = 1 ∧
        X.val.trace = 1 ∧ X.val.det = 1 ∧ (S.val * X.val).trace * (S.val * X.val).trace =
          (S.val * X.val).trace + 1 :=
  exists_lifts_of_order_five f hneg ⟨a5c₁, a5c₂, by decide⟩ ⟨a5c₃, a5c₂, by decide⟩ (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Lemma 3.21 of Sutherland for the projective image `A₅`** (arXiv:1504.07618v7): two subgroups
of `GL₂(𝔽_p)` with projective image `A₅` and the same scalars are conjugate, for odd `p`. The lifts
of a generating pair of type `(2, 3, 5)` with determinant `1` are determined by `σ = tr S X`, a root
of `x² = x + 1`. If the roots for the two subgroups differ, another generating pair, with product
conjugate to the square of `s t`, gives the other root. -/
lemma mem_subgroupConjClass_of_A5 (hp : p ≠ 2) (f : projectiveImage K ≃* alternatingGroup (Fin 5))
    (f' : projectiveImage K' ≃* alternatingGroup (Fin 5))
    (hZ : K ⊓ Subgroup.center _ = K' ⊓ Subgroup.center _) : K' ∈ subgroupConjClass p K := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two p hp
  have hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K := neg_one_mem_of_A5 hp f
  rcases exists_lifts_a5s_a5t hneg f with ⟨S, hS, X, hX, hmS, hmX, htrS, hdS, htrX, hdX, hσ⟩
  rcases exists_lifts_a5s_a5t (neg_one_mem_of_A5 hp f') f' with
    ⟨S', hS', X', hX', hmS', hmX', htrS', hdS', htrX', hdX', hσ'⟩
  have hκ {A B : Matrix (Fin 2) (Fin 2) (ZMod p)} (hA : A.trace = 0) (hdA : A.det = 1)
      (htB : B.trace = 1) (hdB : B.det = 1)
      (hAB : (A * B).trace * (A * B).trace = (A * B).trace + 1) : (A * B - B * A).det ≠ 0 := by
    rw [det_commutator_of_trace_eq_zero hA, hdA, htB, hdB, hAB]
    intro h
    have h₁ : (A * B).trace = 2 := by
      linear_combination -h
    rw [h₁] at hAB
    exact one_ne_zero (by linear_combination hAB : (1 : ZMod p) = 0)
  by_cases hσσ : (S.val * X.val).trace = (S'.val * X'.val).trace
  · rcases exists_mul_eq_mul_of_trace_det_eq h2 htrS htrS' (hdS.trans hdS'.symm)
      (hdS.trans_ne one_ne_zero) (htrX.trans htrX'.symm) (hdX.trans hdX'.symm) hσσ
      (hκ htrS hdS htrX hdX hσ) with ⟨g, hg₁, hg₂⟩
    exact mem_subgroupConjClass_of_lifts f f' closure_a5s_a5t closure_a5s_a5t hZ hS hX hS' hX' hmS
      hmX hmS' hmX' (Units.ext hg₁) (Units.ext hg₂)
  have hsum : (S.val * X.val).trace + (S'.val * X'.val).trace = 1 := by
    have h₁ : ((S.val * X.val).trace - (S'.val * X'.val).trace) *
        ((S.val * X.val).trace + (S'.val * X'.val).trace - 1) = 0 := by
      linear_combination hσ - hσ'
    linear_combination (mul_eq_zero.mp h₁).resolve_left (sub_ne_zero.mpr hσσ)
  rcases exists_lifts_of_order_five f hneg (s := a5s) (t := a5t₁) ⟨a5c₁, a5c₂, by decide⟩
    ⟨a5c₃, a5c₄, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) with ⟨S₁, hS₁, X₁, hX₁, hmS₁, hmX₁, htrS₁, hdS₁, htrX₁, hdX₁, -⟩
  rcases exists_lift f a5y with ⟨Y, -, hmY⟩
  have hV : ProjGenLinGroup.mk (Y * (S * X) ^ 2 * Y⁻¹) = ProjGenLinGroup.mk (S₁ * X₁) := by
    have h₁ : ProjGenLinGroup.mk ((S * X) ^ 2) =
        ((f.symm ((a5s * a5t) ^ 2) : projectiveImage K) : PGL(Fin 2, ZMod p)) := by
      rw [map_pow, mk_mul_of_lift f hmS hmX, ← Subgroup.coe_pow, ← map_pow]
    rw [mk_mul_of_lift f (mk_mul_of_lift f hmY h₁) (mk_inv_of_lift f hmY),
      mk_mul_of_lift f hmS₁ hmX₁]
    exact congrArg (fun z ↦ ((f.symm z : projectiveImage K) : PGL(Fin 2, ZMod p))) (by decide)
  rcases ProjGenLinGroup.mk_eq_mk_iff.mp hV with ⟨z, hz⟩
  have hdU : (S * X).val.det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdS, hdX, mul_one]
  have hdV : det (Y * (S * X) ^ 2 * Y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_pow, det_eq_one_of_val_det hdU, one_pow, mul_one, map_inv,
      mul_inv_cancel]
  have hdU₁ : det (S₁ * X₁) = 1 := det_eq_one_of_val_det <| by
    rw [Units.val_mul, Matrix.det_mul, hdS₁, hdX₁, mul_one]
  have hz₂ : (z : ZMod p) * z = 1 := by
    have h₁ : det (Y * (S * X) ^ 2 * Y⁻¹ * scalar (Fin 2) z) = det (S₁ * X₁) := congrArg det hz
    rw [map_mul, hdV, one_mul, det_scalar, Fintype.card_fin, hdU₁] at h₁
    rw [← Units.val_mul, ← sq, h₁, Units.val_one]
  have htr₁ : (S₁.val * X₁.val).trace = z * ((S.val * X.val).trace - 1) := by
    have h₁ : S₁.val * X₁.val = (z : ZMod p) • (Y * (S * X) ^ 2 * Y⁻¹).val := by
      rw [← Units.val_mul, ← hz, val_mul_scalar]
    have h₂ : (Y * (S * X) ^ 2 * Y⁻¹).val.trace = ((S * X) ^ 2).val.trace :=
      Matrix.trace_units_conj Y ((S * X) ^ 2).val
    have h₃ : ((S * X) ^ 2).val.trace = (S.val * X.val).trace * (S.val * X.val).trace - 2 := by
      rw [Units.val_pow_eq_pow_val, sq_eq_trace_smul_sub_det_smul_one_fin_two, trace_sub,
        trace_smul, trace_smul, trace_one, Fintype.card_fin, hdU, Units.val_mul]
      simp
    rw [h₁, trace_smul, h₂, h₃, hσ, smul_eq_mul]
    ring1
  have hex : ∃ S₂ ∈ K, ProjGenLinGroup.mk S₂ = (f.symm a5s : PGL(Fin 2, ZMod p)) ∧
      S₂.val.trace = 0 ∧ S₂.val.det = 1 ∧ (S₂.val * X₁.val).trace = (S'.val * X'.val).trace := by
    rcases mul_self_eq_one_iff.mp hz₂ with hz₁ | hz₁
    · refine ⟨-S₁, neg_mem_of_neg_one_mem hneg hS₁, by rw [mk_neg, hmS₁], by
        rw [trace_val_neg, htrS₁, neg_zero], by rw [det_val_neg, hdS₁], ?_⟩
      rw [trace_val_neg_mul, htr₁, hz₁]
      linear_combination -hsum
    · refine ⟨S₁, hS₁, hmS₁, htrS₁, hdS₁, ?_⟩
      rw [htr₁, hz₁]
      linear_combination -hsum
  rcases hex with ⟨S₂, hS₂, hmS₂, htrS₂, hdS₂, htr₂⟩
  rcases exists_mul_eq_mul_of_trace_det_eq h2 htrS₂ htrS' (hdS₂.trans hdS'.symm)
    (hdS₂.trans_ne one_ne_zero) (htrX₁.trans htrX'.symm) (hdX₁.trans hdX'.symm) htr₂
    (hκ htrS₂ hdS₂ htrX₁ hdX₁ (by rw [htr₂]; exact hσ')) with ⟨g, hg₁, hg₂⟩
  exact mem_subgroupConjClass_of_lifts f f' closure_a5s_a5t₁ closure_a5s_a5t hZ hS₂ hX₁ hS' hX' hmS₂
    hmX₁ hmS' hmX' (Units.ext hg₁) (Units.ext hg₂)

/-- **The index `[det K : det Z]` is `1` for a projective image `A₅`** (Lemma 3.21 (3c) of
Sutherland, arXiv:1504.07618v7), a generating pair being a pair of commutators. -/
lemma detCenterIndex_eq_one_of_A5 (hp : p ≠ 2) (f : projectiveImage K ≃* alternatingGroup (Fin 5)) :
    detCenterIndex p K = 1 := by
  rcases exists_lifts_a5s_a5t (neg_one_mem_of_A5 hp f) f with
    ⟨S, hS, X, hX, hmS, hmX, -, hdS, -, hdX, -⟩
  refine detCenterIndex_eq_one_of_lifts f closure_a5s_a5t hS hX hmS hmX ?_ ?_
  · rw [det_eq_one_of_val_det hdS]
    exact one_mem _
  · rw [det_eq_one_of_val_det hdX]
    exact one_mem _

/-- The element `(0 1)(2 3)` of `A₄`. -/
private def a4s : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- The element `(0 2)(1 3)` of `A₄`. -/
private def a4v : alternatingGroup (Fin 4) :=
  ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- A `3`-cycle of `A₄`. -/
private def a4t : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- An element of `A₄` used to write `a4s` as a commutator. -/
private def a4c₁ : alternatingGroup (Fin 4) :=
  ⟨swap 1 2 * swap 2 3, Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- An element of `A₄` used to write `a4s` as a commutator. -/
private def a4c₂ : alternatingGroup (Fin 4) :=
  ⟨swap 0 2 * swap 2 1, Perm.mem_alternatingGroup.mpr (by decide)⟩

private lemma closure_a4s_a4t :
    Subgroup.closure ({a4s, a4t} : Set (alternatingGroup (Fin 4))) = ⊤ := by
  have hw : ∀ x : alternatingGroup (Fin 4), ∃ i j k : Fin 3, ∃ m l : Fin 2,
      x = a4t ^ (i : ℕ) * a4s ^ (m : ℕ) * a4t ^ (j : ℕ) * a4s ^ (l : ℕ) * a4t ^ (k : ℕ) := by
    decide +kernel
  have hs : a4s ∈ Subgroup.closure ({a4s, a4t} : Set (alternatingGroup (Fin 4))) :=
    Subgroup.subset_closure (by simp)
  have ht : a4t ∈ Subgroup.closure ({a4s, a4t} : Set (alternatingGroup (Fin 4))) :=
    Subgroup.subset_closure (by simp)
  refine eq_top_iff.mpr fun x _ ↦ ?_
  rcases hw x with ⟨i, j, k, m, l, rfl⟩
  exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem ht _) (pow_mem hs _)) (pow_mem ht _))
    (pow_mem hs _)) (pow_mem ht _)

private lemma closure_a4s_a4t_inv :
    Subgroup.closure ({a4s, a4t⁻¹} : Set (alternatingGroup (Fin 4))) = ⊤ := by
  rw [eq_top_iff, ← closure_a4s_a4t, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.subset_closure (by simp)
  · simpa using inv_mem (Subgroup.subset_closure (by simp) :
      a4t⁻¹ ∈ Subgroup.closure ({a4s, a4t⁻¹} : Set (alternatingGroup (Fin 4))))

lemma exists_lift_of_order_three (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K)
    (hs : ∃ a b : T, a * b * a⁻¹ * b⁻¹ = s) (hs₂ : s ^ 2 = 1) (hs₁ : s ≠ 1) (hu₃ : (s * t) ^ 3 = 1)
    (hu₁ : s * t ≠ 1) (hmX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p)))
    (hdX : X.val.det = X.val.trace * X.val.trace) :
    ∃ S ∈ K, ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p)) ∧ S.val.trace = 0 ∧
      S.val.det = 1 ∧ (S.val * X.val).trace = X.val.trace := by
  rcases exists_lift_det_eq_one e hs with ⟨S₀, hS₀, hmS₀, hdS₀⟩
  have hval : S₀.val.det = 1 := val_det_eq_one_of_det hdS₀
  have htrS : S₀.val.trace = 0 := trace_eq_zero_of_sq_mem_center
    (notMem_center_of_lift e hmS₀ hs₁) (pow_mem_center_of_lift e hmS₀ hs₂)
  have hmU : ProjGenLinGroup.mk (S₀ * X) = (e.symm (s * t) : PGL(Fin 2, ZMod p)) :=
    mk_mul_of_lift e hmS₀ hmX
  have h₁ : (S₀ * X).val.trace * (S₀ * X).val.trace = (S₀ * X).val.det :=
    trace_mul_self_eq_det_of_pow_three_mem_center (notMem_center_of_lift e hmU hu₁)
      (pow_mem_center_of_lift e hmU hu₃)
  rw [Units.val_mul, Matrix.det_mul, hval, one_mul, hdX] at h₁
  rcases mul_self_eq_mul_self_iff.mp h₁ with h | h
  · exact ⟨S₀, hS₀, hmS₀, htrS, hval, h⟩
  · exact ⟨-S₀, neg_mem_of_neg_one_mem hneg hS₀, by rw [mk_neg, hmS₀], by
      rw [trace_val_neg, htrS, neg_zero], by rw [det_val_neg, hval], by
      rw [trace_val_neg_mul, h, neg_neg]⟩

private lemma mem_subgroupConjClass_of_order_three (hp : p ≠ 2)
    (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K) (hneg' : (-1 : GL (Fin 2) (ZMod p)) ∈ K')
    (hgen : Subgroup.closure ({s, t} : Set T) = ⊤)
    (hgen' : Subgroup.closure ({s', t'} : Set T') = ⊤)
    (hZ : K ⊓ Subgroup.center _ = K' ⊓ Subgroup.center _) (hs : ∃ a b : T, a * b * a⁻¹ * b⁻¹ = s)
    (hs₂ : s ^ 2 = 1) (hs₁ : s ≠ 1) (hu₃ : (s * t) ^ 3 = 1) (hu₁ : s * t ≠ 1)
    (hs' : ∃ a b : T', a * b * a⁻¹ * b⁻¹ = s') (hs'₂ : s' ^ 2 = 1) (hs'₁ : s' ≠ 1)
    (hu'₃ : (s' * t') ^ 3 = 1) (hu'₁ : s' * t' ≠ 1) (hXK : X ∈ K) (hX'K : X' ∈ K')
    (hmX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p)))
    (hmX' : ProjGenLinGroup.mk X' = (e'.symm t' : PGL(Fin 2, ZMod p)))
    (hdX : X.val.det = X.val.trace * X.val.trace) (hdX' : X'.val.det = X'.val.trace * X'.val.trace)
    (hz : scalar (Fin 2) z ∈ K') (hzt : X'.val.trace * z = X.val.trace) :
    K' ∈ subgroupConjClass p K := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two p hp
  have hτ : X.val.trace ≠ 0 := fun h ↦ (isUnits_det_units X).ne_zero (by rw [hdX, h, mul_zero])
  have htrX'' : (X' * scalar (Fin 2) z).val.trace = X.val.trace := by
    rw [val_mul_scalar, trace_smul, smul_eq_mul, mul_comm, hzt]
  have hdX'' : (X' * scalar (Fin 2) z).val.det = X.val.det := by
    rw [val_mul_scalar, det_smul, hdX', hdX, Fintype.card_fin, ← hzt]
    ring1
  have hmX'' : ProjGenLinGroup.mk (X' * scalar (Fin 2) z) = (e'.symm t' : PGL(Fin 2, ZMod p)) :=
    mk_eq_mk_of_lift_eq e' hmX'
  rcases exists_lift_of_order_three e hneg hs hs₂ hs₁ hu₃ hu₁ hmX hdX with
    ⟨S, hS, hmS, htrS, hdS, htrSX⟩
  rcases exists_lift_of_order_three e' hneg' hs' hs'₂ hs'₁ hu'₃ hu'₁ hmX''
    (by rw [hdX'', htrX'', hdX]) with ⟨S', hS', hmS', htrS', hdS', htrSX'⟩
  rcases exists_mul_eq_mul_of_trace_det_eq h2 htrS htrS' (hdS.trans hdS'.symm)
    (hdS.trans_ne one_ne_zero) htrX''.symm hdX''.symm
    (htrSX.trans (htrX''.symm.trans htrSX'.symm)) (by
      rw [det_commutator_of_trace_eq_zero htrS, hdS, htrSX, hdX]
      intro h
      exact mul_ne_zero h2 (mul_ne_zero hτ hτ) (by linear_combination h)) with ⟨g, hg₁, hg₂⟩
  exact mem_subgroupConjClass_of_lifts e e' hgen hgen' hZ hS hXK hS' (mul_mem hX'K hz) hmS hmX hmS'
    hmX'' (Units.ext hg₁) (Units.ext hg₂)

lemma eq_or_eq_inv_of_pow_three_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G] {x y : G}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx₁ : x ≠ 1) (hy₁ : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hne
  push Not at hne
  have hinv : x ≠ x⁻¹ := fun h ↦ hx₁ <| by
    have h₁ : x * x = 1 := by
      nth_rw 2 [h]
      exact mul_inv_cancel x
    have h₂ : x ^ 3 = x := by
      rw [pow_succ, sq, h₁, one_mul]
    rw [← h₂, hx]
  have hsub : ({1, x, x⁻¹, y} : Finset G) ⊆ Finset.univ.filter fun a : G ↦ a ^ 3 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · exact hx
    · rw [inv_pow, hx, inv_one]
    · exact hy
  have hcard : ({1, x, x⁻¹, y} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hne.2.symm
    · simp [hinv, hne.1.symm]
    · simp [hx₁, hx₁.symm, hy₁.symm]
  have hle : (Finset.univ.filter fun a : G ↦ a ^ 3 = 1).card ≤ 3 :=
    IsCyclic.card_pow_eq_one_le three_pos
  have hle' : ({1, x, x⁻¹, y} : Finset G).card ≤ (Finset.univ.filter fun a : G ↦ a ^ 3 = 1).card :=
    Finset.card_le_card hsub
  omega

lemma val_inv_trace (hdX : X.val.det = X.val.trace * X.val.trace) :
    (X⁻¹).val.trace = X.val.trace⁻¹ := by
  rw [Matrix.coe_units_inv, inv_apply_of_field, trace_smul, hdX, smul_eq_mul, trace_fin_two_of]
  have h₁ : X 1 1 + X 0 0 = X.val.trace := by
    rw [trace_fin_two, add_comm]
  rw [h₁]
  field_simp

lemma val_inv_det : (X⁻¹).val.det = X.val.det⁻¹ := by
  rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

lemma neg_one_mem_of_A4 (hp : p ≠ 2) (f : projectiveImage K ≃* alternatingGroup (Fin 4)) :
    (-1 : GL (Fin 2) (ZMod p)) ∈ K :=
  neg_one_mem_of_lifts f hp (s₁ := a4s) (s₂ := a4v) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

private lemma exists_lift_of_A4 (hp : p ≠ 2) (f : projectiveImage K ≃* alternatingGroup (Fin 4)) :
    ∃ X ∈ K, ∃ τ : (ZMod p)ˣ, ProjGenLinGroup.mk X = (f.symm a4t : PGL(Fin 2, ZMod p)) ∧
      X.val.trace = τ ∧ X.val.det = τ * τ ∧ scalar (Fin 2) (τ ^ 3) ∈ K ∧
        (detCenterIndex p K = 1 ↔ scalar (Fin 2) τ ∈ K) := by
  rcases exists_lift f a4t with ⟨X, hX, hmX⟩
  have hdX : X.val.trace * X.val.trace = X.val.det :=
    trace_mul_self_eq_det_of_pow_three_mem_center (notMem_center_of_lift f hmX (by decide))
      (pow_mem_center_of_lift f hmX (by decide))
  have hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K := neg_one_mem_of_A4 hp f
  have hτ : X.val.trace ≠ 0 := fun h ↦ (isUnits_det_units X).ne_zero <| by
    rw [← hdX, h, mul_zero]
  refine ⟨X, hX, Units.mk0 _ hτ, hmX, rfl, hdX.symm, ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · have hcube : X ^ 3 = -(scalar (Fin 2) (Units.mk0 _ hτ ^ 3) : GL (Fin 2) (ZMod p)) :=
      Units.ext <| by
        rw [Units.val_pow_eq_pow_val, pow_add_two_fin_two _ 1, pow_add_two_fin_two _ 0, pow_one,
          pow_zero, ← hdX, val_neg_of_field, val_scalar_eq_smul, Units.val_pow_eq_pow_val,
          Units.val_mk0]
        module
    have h₁ : -X ^ 3 ∈ K := neg_mem_of_neg_one_mem hneg (pow_mem hX 3)
    rwa [hcube, neg_neg] at h₁
  · have h₂ : K.map det ≤ (K ⊓ Subgroup.center _).map det := by
      rwa [detCenterIndex, Subgroup.relIndex_eq_one] at h
    rcases mem_map_det_inf_center_iff.mp (h₂ (Subgroup.mem_map_of_mem _ hX)) with ⟨w, hw, hwX⟩
    refine scalar_mem_of_sq_eq hneg hw (Units.ext ?_)
    rw [hwX, val_det_apply, ← hdX, Units.val_pow_eq_pow_val, Units.val_mk0, sq]
  · rcases exists_lift_of_order_three f hneg (s := a4s) (t := a4t) ⟨a4c₁, a4c₂, by decide⟩
      (by decide) (by decide) (by decide) (by decide) hmX hdX.symm with
      ⟨S, hS, hmS, -, hdS, -⟩
    refine detCenterIndex_eq_one_of_lifts f closure_a4s_a4t hS hX hmS hmX ?_ ?_
    · rw [det_eq_one_of_val_det hdS]
      exact one_mem _
    · refine mem_map_det_inf_center_iff.mpr ⟨Units.mk0 _ hτ, h, Units.ext ?_⟩
      rw [val_det_apply, ← hdX, Units.val_pow_eq_pow_val, Units.val_mk0, sq]

/-- **Lemma 3.21 of Sutherland for the projective image `A₄`** (arXiv:1504.07618v7): two subgroups
of `GL₂(𝔽_p)` with projective image `A₄`, the same scalars and the same value of "`[det K : det Z]`
is `1`" are conjugate, for odd `p`. The value is `1` exactly when the trace `τ` of a lift of a
`3`-cycle is a scalar of the group; its cube always is, and in the cyclic group `𝔽_pˣ / Z` the
elements of order `3` are `x` and `x⁻¹`; the case `x⁻¹` is obtained from the generating pair
`(s, t⁻¹)`. -/
lemma mem_subgroupConjClass_of_A4 (hp : p ≠ 2) (f : projectiveImage K ≃* alternatingGroup (Fin 4))
    (f' : projectiveImage K' ≃* alternatingGroup (Fin 4))
    (hZ : K ⊓ Subgroup.center _ = K' ⊓ Subgroup.center _)
    (ha : detCenterIndex p K = 1 ↔ detCenterIndex p K' = 1) : K' ∈ subgroupConjClass p K := by
  rcases exists_lift_of_A4 hp f with ⟨X, hX, τ, hmX, htrX, hdX, hcube, hiff⟩
  rcases exists_lift_of_A4 hp f' with ⟨X', hX', τ', hmX', htrX', hdX', hcube', hiff'⟩
  have hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K := neg_one_mem_of_A4 hp f
  have hneg' : (-1 : GL (Fin 2) (ZMod p)) ∈ K' := neg_one_mem_of_A4 hp f'
  have hdXt : X.val.det = X.val.trace * X.val.trace := by
    rw [hdX, htrX]
  have hdXt' : X'.val.det = X'.val.trace * X'.val.trace := by
    rw [hdX', htrX']
  have hcore {z : (ZMod p)ˣ} (hz : scalar (Fin 2) z ∈ K') (hzt : τ' * z = τ) :
      K' ∈ subgroupConjClass p K :=
    mem_subgroupConjClass_of_order_three f f' hp hneg hneg' closure_a4s_a4t closure_a4s_a4t hZ
      ⟨a4c₁, a4c₂, by decide⟩ (by decide) (by decide) (by decide) (by decide)
      ⟨a4c₁, a4c₂, by decide⟩ (by decide) (by decide) (by decide) (by decide) hX hX' hmX hmX' hdXt
      hdXt' hz (by rw [htrX', htrX, ← hzt, Units.val_mul])
  by_cases hτ : scalar (Fin 2) τ ∈ K
  · refine hcore (z := τ'⁻¹ * τ) ?_ (by rw [mul_inv_cancel_left])
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem (hiff'.mp (ha.mp (hiff.mpr hτ))))
      ((scalar_mem_iff_of_inf_center_eq hZ).mp hτ)
  have hτ' : scalar (Fin 2) τ' ∉ K' := fun h ↦ hτ (hiff.mp (ha.mpr (hiff'.mpr h)))
  have hmem {w : (ZMod p)ˣ} : (w : (ZMod p)ˣ ⧸ K'.comap (scalar (Fin 2))) = 1 ↔
      scalar (Fin 2) w ∈ K' := QuotientGroup.eq_one_iff w
  have hx : ((τ : (ZMod p)ˣ) : (ZMod p)ˣ ⧸ K'.comap (scalar (Fin 2))) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hmem]
    exact (scalar_mem_iff_of_inf_center_eq hZ).mp hcube
  have hy : ((τ' : (ZMod p)ˣ) : (ZMod p)ˣ ⧸ K'.comap (scalar (Fin 2))) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hmem]
    exact hcube'
  have : IsCyclic ((ZMod p)ˣ ⧸ K'.comap (scalar (Fin 2))) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rcases eq_or_eq_inv_of_pow_three_eq_one hx hy
    (fun h ↦ hτ ((scalar_mem_iff_of_inf_center_eq hZ).mpr (hmem.mp h)))
    (fun h ↦ hτ' (hmem.mp h)) with h | h
  · exact hcore (z := τ'⁻¹ * τ) (QuotientGroup.eq.mp h) (by rw [mul_inv_cancel_left])
  · have h₁ : scalar (Fin 2) (τ'⁻¹ * τ⁻¹) ∈ K' := by
      rw [← QuotientGroup.mk_inv] at h
      exact QuotientGroup.eq.mp h
    refine mem_subgroupConjClass_of_order_three f f' hp hneg hneg' (X := X⁻¹) (s := a4s)
      (t := a4t⁻¹) (s' := a4s) (t' := a4t) closure_a4s_a4t_inv closure_a4s_a4t hZ
      ⟨a4c₁, a4c₂, by decide⟩ (by decide) (by decide) (by decide) (by decide)
      ⟨a4c₁, a4c₂, by decide⟩ (by decide) (by decide) (by decide) (by decide) (inv_mem hX) hX'
      (mk_inv_of_lift f hmX) hmX' ?_ hdXt' h₁ ?_
    · rw [val_inv_det, val_inv_trace hdXt, hdXt, mul_inv]
    · rw [val_inv_trace hdXt, htrX', htrX, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val]
      field_simp

/-- The transposition `(0 1)` of `S₄`. -/
private def s4s : Perm (Fin 4) :=
  swap 0 1

/-- A `3`-cycle of `S₄`, with `s4s * s4t` a `4`-cycle. -/
private def s4t : Perm (Fin 4) :=
  swap 1 2 * swap 2 3

private lemma closure_s4s_s4t : Subgroup.closure ({s4s, s4t} : Set (Perm (Fin 4))) = ⊤ := by
  have hw : ∀ x : Perm (Fin 4), ∃ i j k l : Fin 3, ∃ m n o : Fin 2,
      x = s4t ^ (i : ℕ) * s4s ^ (m : ℕ) * s4t ^ (j : ℕ) * s4s ^ (n : ℕ) * s4t ^ (k : ℕ) *
        s4s ^ (o : ℕ) * s4t ^ (l : ℕ) := by
    decide +kernel
  have hs : s4s ∈ Subgroup.closure ({s4s, s4t} : Set (Perm (Fin 4))) :=
    Subgroup.subset_closure (by simp)
  have ht : s4t ∈ Subgroup.closure ({s4s, s4t} : Set (Perm (Fin 4))) :=
    Subgroup.subset_closure (by simp)
  refine eq_top_iff.mpr fun x _ ↦ ?_
  rcases hw x with ⟨i, j, k, l, m, n, o, rfl⟩
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem ht _) (pow_mem hs _))
    (pow_mem ht _)) (pow_mem hs _)) (pow_mem ht _)) (pow_mem hs _)) (pow_mem ht _)

lemma neg_one_mem_of_S4 (hp : p ≠ 2) (f : projectiveImage K ≃* Perm (Fin 4)) :
    (-1 : GL (Fin 2) (ZMod p)) ∈ K :=
  neg_one_mem_of_lifts f hp (s₁ := swap 0 1 * swap 2 3) (s₂ := swap 0 2 * swap 1 3) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

private lemma exists_lifts_of_S4 (hp : p ≠ 2) (f : projectiveImage K ≃* Perm (Fin 4)) :
    ∃ S ∈ K, ∃ X ∈ K, ∃ D : (ZMod p)ˣ, ProjGenLinGroup.mk S = (f.symm s4s : PGL(Fin 2, ZMod p)) ∧
      ProjGenLinGroup.mk X = (f.symm s4t : PGL(Fin 2, ZMod p)) ∧ S.val.trace = 0 ∧
        X.val.trace = 1 ∧ X.val.det = 1 ∧ S.val.det = D ∧
          (S.val * X.val).trace * (S.val * X.val).trace = 2 * D ∧ scalar (Fin 2) D ∈ K ∧
            (detCenterIndex p K = 1 ↔ ∃ w, scalar (Fin 2) w ∈ K ∧ w ^ 2 = D) := by
  have hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K := neg_one_mem_of_S4 hp f
  rcases exists_lift_trace_eq_one f hneg (t := s4t) ⟨swap 2 3, swap 1 2, by decide⟩ (by decide)
    (by decide) with ⟨X, hX, hmX, htrX, hdX⟩
  rcases exists_lift f s4s with ⟨S, hS, hmS⟩
  have htrS : S.val.trace = 0 := trace_eq_zero_of_sq_mem_center
    (notMem_center_of_lift f hmS (by decide)) (pow_mem_center_of_lift f hmS (by decide))
  have hmU : ProjGenLinGroup.mk (S * X) = (f.symm (s4s * s4t) : PGL(Fin 2, ZMod p)) :=
    mk_mul_of_lift f hmS hmX
  have hmU₂ : ProjGenLinGroup.mk ((S * X) ^ 2) =
      ((f.symm ((s4s * s4t) ^ 2) : projectiveImage K) : PGL(Fin 2, ZMod p)) := by
    rw [map_pow, hmU, ← Subgroup.coe_pow, ← map_pow]
  have hσ : (S * X).val.trace * (S * X).val.trace = 2 * (S * X).val.det :=
    trace_mul_self_eq_two_mul_det_of_pow_four_mem_center (notMem_center_of_lift f hmU₂ (by decide))
      (pow_mem_center_of_lift f hmU (by decide))
  rw [Units.val_mul, Matrix.det_mul, hdX, mul_one] at hσ
  have hdet₀ : S.val.det ≠ 0 := (isUnits_det_units S).ne_zero
  have hdS : det S = Units.mk0 _ hdet₀ := Units.ext (val_det_apply S)
  have hsq : S * S = -(scalar (Fin 2) (Units.mk0 _ hdet₀) : GL (Fin 2) (ZMod p)) := Units.ext <| by
    rw [Units.val_mul, ← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, htrS, zero_smul, zero_sub,
      val_neg_of_field, val_scalar_eq_smul, Units.val_mk0]
  have hscal : scalar (Fin 2) (Units.mk0 _ hdet₀) ∈ K := by
    have h₁ : -(S * S) ∈ K := neg_mem_of_neg_one_mem hneg (mul_mem hS hS)
    rwa [hsq, neg_neg] at h₁
  refine ⟨S, hS, X, hX, Units.mk0 _ hdet₀, hmS, hmX, htrS, htrX, hdX, rfl, hσ, hscal, fun h ↦ ?_,
    fun ⟨w, hw, hwD⟩ ↦ ?_⟩
  · have h₂ : K.map det ≤ (K ⊓ Subgroup.center _).map det := by
      rwa [detCenterIndex, Subgroup.relIndex_eq_one] at h
    exact mem_map_det_inf_center_iff.mp (hdS ▸ h₂ (Subgroup.mem_map_of_mem _ hS))
  · refine detCenterIndex_eq_one_of_lifts f closure_s4s_s4t hS hX hmS hmX ?_ ?_
    · rw [hdS]
      exact mem_map_det_inf_center_iff.mpr ⟨w, hw, hwD⟩
    · rw [det_eq_one_of_val_det hdX]
      exact one_mem _

/-- **Lemma 3.21 of Sutherland for the projective image `S₄`** (arXiv:1504.07618v7): two subgroups
of `GL₂(𝔽_p)` with projective image `S₄`, the same scalars and the same value of "`[det K : det Z]`
is `1`" are conjugate, for odd `p`: the determinants `D`, `D'` of the lifts of the transposition are
both squares of scalars or both not, so their quotient is the square of a scalar, and the lifts can
be scaled to the same traces and determinants. -/
lemma mem_subgroupConjClass_of_S4 (hp : p ≠ 2) (f : projectiveImage K ≃* Perm (Fin 4))
    (f' : projectiveImage K' ≃* Perm (Fin 4)) (hZ : K ⊓ Subgroup.center _ = K' ⊓ Subgroup.center _)
    (ha : detCenterIndex p K = 1 ↔ detCenterIndex p K' = 1) : K' ∈ subgroupConjClass p K := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two p hp
  rcases exists_lifts_of_S4 hp f with
    ⟨S, hS, X, hX, D, hmS, hmX, htrS, htrX, hdX, hdS, hσ, hD, hiff⟩
  rcases exists_lifts_of_S4 hp f' with
    ⟨S', hS', X', hX', D', hmS', hmX', htrS', htrX', hdX', hdS', hσ', hD', hiff'⟩
  have hZu {w : (ZMod p)ˣ} : scalar (Fin 2) w ∈ K ↔ scalar (Fin 2) w ∈ K' :=
    scalar_mem_iff_of_inf_center_eq hZ
  have hsq : ∃ z, scalar (Fin 2) z ∈ K' ∧ z ^ 2 * D' = D := by
    by_cases h₁ : ∃ w, scalar (Fin 2) w ∈ K ∧ w ^ 2 = D
    · rcases h₁ with ⟨w, hw, hwD⟩
      rcases hiff'.mp (ha.mp (hiff.mpr ⟨w, hw, hwD⟩)) with ⟨w', hw', hw'D⟩
      refine ⟨w * w'⁻¹, ?_, ?_⟩
      · rw [map_mul, map_inv]
        exact mul_mem (hZu.mp hw) (inv_mem hw')
      · rw [mul_pow, inv_pow, hw'D, inv_mul_cancel_right, hwD]
    · have h₂ : ¬∃ w, scalar (Fin 2) w ∈ K' ∧ w ^ 2 = D' :=
        fun h ↦ h₁ (hiff.mp (ha.mpr (hiff'.mpr h)))
      rcases exists_mem_zpowers_iff_scalar_mem K' with ⟨ζ, hmem⟩
      rcases exists_sq_eq_mul_of_not_exists_sq (ζ := ζ) (a := D) (b := D') (hmem.mpr (hZu.mp hD))
        (hmem.mpr hD') (fun ⟨w, hw, hwD⟩ ↦ h₁ ⟨w, hZu.mpr (hmem.mp hw), hwD⟩)
        (fun ⟨w, hw, hwD⟩ ↦ h₂ ⟨w, hmem.mp hw, hwD⟩) with ⟨w, hw, hwe⟩
      refine ⟨w * D'⁻¹, ?_, ?_⟩
      · rw [map_mul, map_inv]
        exact mul_mem (hmem.mp hw) (inv_mem hD')
      · rw [mul_pow, inv_pow, hwe]
        group
  rcases hsq with ⟨z, hz, hzD⟩
  have hzv : (z : ZMod p) * z * D' = D := by
    rw [← Units.val_mul, ← Units.val_mul, ← sq, hzD]
  have hcase : ((z : ZMod p) * (S'.val * X'.val).trace) * ((z : ZMod p) * (S'.val * X'.val).trace) =
      (S.val * X.val).trace * (S.val * X.val).trace := by
    rw [hσ, ← hzv]
    linear_combination (z : ZMod p) * z * hσ'
  have hex : ∃ S'' ∈ K', ProjGenLinGroup.mk S'' = (f'.symm s4s : PGL(Fin 2, ZMod p)) ∧
      S''.val.trace = 0 ∧ S''.val.det = D ∧ (S''.val * X'.val).trace = (S.val * X.val).trace := by
    have hdet'' : (S' * scalar (Fin 2) z).val.det = D := by
      rw [val_mul_scalar, det_smul, Fintype.card_fin, hdS', ← hzv, sq]
    have htr'' : (S' * scalar (Fin 2) z).val.trace = 0 := by
      rw [val_mul_scalar, trace_smul, htrS', smul_zero]
    have hm'' : ProjGenLinGroup.mk (S' * scalar (Fin 2) z) = (f'.symm s4s : PGL(Fin 2, ZMod p)) :=
      mk_eq_mk_of_lift_eq f' hmS'
    have hmul : ((S' * scalar (Fin 2) z).val * X'.val).trace =
        (z : ZMod p) * (S'.val * X'.val).trace := by
      rw [val_mul_scalar, Matrix.smul_mul, trace_smul, smul_eq_mul]
    rcases mul_self_eq_mul_self_iff.mp hcase with h | h
    · exact ⟨_, mul_mem hS' hz, hm'', htr'', hdet'', by rw [hmul, h]⟩
    · exact ⟨-(S' * scalar (Fin 2) z), neg_mem_of_neg_one_mem (neg_one_mem_of_S4 hp f')
        (mul_mem hS' hz), by rw [mk_neg, hm''], by rw [trace_val_neg, htr'', neg_zero], by
        rw [det_val_neg, hdet''], by rw [trace_val_neg_mul, hmul, h, neg_neg]⟩
  rcases hex with ⟨S'', hS'', hmS'', htrS'', hdS'', htrm⟩
  rcases exists_mul_eq_mul_of_trace_det_eq h2 htrS htrS'' (hdS.trans hdS''.symm)
    (hdS.trans_ne D.ne_zero) (htrX.trans htrX'.symm) (hdX.trans hdX'.symm) htrm.symm (by
      rw [det_commutator_of_trace_eq_zero htrS, hdS, htrX, hdX, hσ]
      intro h
      exact D.ne_zero (by linear_combination h)) with ⟨g, hg₁, hg₂⟩
  exact mem_subgroupConjClass_of_lifts f f' closure_s4s_s4t closure_s4s_s4t hZ hS hX hS'' hX' hmS
    hmX hmS'' hmX' (Units.ext hg₁) (Units.ext hg₂)

/-- **The index `[det K : det Z]` is `1` or `2` for a projective image `S₄`** (Lemma 3.21 (3b) of
Sutherland, arXiv:1504.07618v7). -/
lemma detCenterIndex_eq_one_or_two_of_S4 (hp : p ≠ 2) (f : projectiveImage K ≃* Perm (Fin 4)) :
    detCenterIndex p K = 1 ∨ detCenterIndex p K = 2 := by
  rcases exists_lifts_of_S4 hp f with ⟨S, hS, X, hX, D, hmS, hmX, -, -, hdX, hdS, -, hD, hiff⟩
  by_cases h₁ : ∃ w, scalar (Fin 2) w ∈ K ∧ w ^ 2 = D
  · exact Or.inl (hiff.mpr h₁)
  refine Or.inr ?_
  have hD₀ : D ∉ (K ⊓ Subgroup.center _).map det := fun h ↦ h₁ (mem_map_det_inf_center_iff.mp h)
  have hD₂ : D * D ∈ (K ⊓ Subgroup.center _).map det :=
    mem_map_det_inf_center_iff.mpr ⟨D, hD, sq D⟩
  let E : Subgroup (ZMod p)ˣ :=
    { carrier := {b | b ∈ (K ⊓ Subgroup.center _).map det ∨
        b * D ∈ (K ⊓ Subgroup.center _).map det}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr (by simpa only [mul_assoc] using mul_mem ha hb)
        · exact Or.inr (by simpa only [mul_right_comm a b D] using mul_mem ha hb)
        · refine Or.inl ?_
          have h₂ : a * D * (b * D) * (D * D)⁻¹ ∈ (K ⊓ Subgroup.center _).map det :=
            mul_mem (mul_mem ha hb) (inv_mem hD₂)
          rwa [mul_mul_mul_comm, mul_inv_cancel_right] at h₂
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ?_
          have h₂ : (a * D)⁻¹ * (D * D) ∈ (K ⊓ Subgroup.center _).map det :=
            mul_mem (inv_mem ha) hD₂
          rwa [mul_inv, mul_assoc, inv_mul_cancel_left] at h₂ }
  have hdSu : det S = D := Units.ext (by rw [val_det_apply, hdS])
  have hall : K ≤ E.comap det := le_of_lifts_mem f closure_s4s_s4t (fun z hz ↦
    Or.inl (Subgroup.mem_map_of_mem _ hz)) hS hX (Or.inr (by rwa [hdSu]))
    (Or.inl (by rw [det_eq_one_of_val_det hdX]; exact one_mem _)) hmS hmX
  rw [detCenterIndex, Subgroup.relIndex_eq_two_iff]
  refine ⟨D, ⟨S, hS, hdSu⟩, fun b hb ↦ ?_⟩
  rcases hb with ⟨k, hk, rfl⟩
  rcases hall hk with h | h
  · refine Or.inr ⟨h, fun h₂ ↦ hD₀ ?_⟩
    have h₃ : (det k)⁻¹ * (det k * D) ∈ (K ⊓ Subgroup.center _).map det := mul_mem (inv_mem h) h₂
    rwa [inv_mul_cancel_left] at h₃
  · refine Or.inl ⟨h, fun h₂ ↦ hD₀ ?_⟩
    have h₃ : (det k)⁻¹ * (det k * D) ∈ (K ⊓ Subgroup.center _).map det := mul_mem (inv_mem h₂) h
    rwa [inv_mul_cancel_left] at h₃

end Matrix.GeneralLinearGroup
