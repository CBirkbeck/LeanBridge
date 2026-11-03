import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.FiniteAdelicAlgebra
import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod

/-!
# The comparison of `Ô ⊗ ℚ` with `B ⊗_ℤ ℤ̂`

The LMFDB (knowl `shimcurve`) defines `Ô = O ⊗_ℤ ℤ̂` and `B̂ = B ⊗_ℤ ℤ̂`, while
`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.FiniteAdelicAlgebra` builds them as the inverse
limit `Ô = lim_N O/NO` and its localization `B̂ = Ô[1/n : n ≥ 1]`. This file proves that these
agree, with the ring `ℤ̂` of profinite integers of Tau Ceti (`TauCeti.zHat`): for an order `O` of a
quaternion algebra `B` over `ℚ`, `x ⊗ z ↦ x z` is a ring isomorphism `B ⊗_ℤ ℤ̂ ≃ B̂` carrying the
image of `O ⊗_ℤ ℤ̂` onto `Ô`. Since `B` is a `ℚ`-vector space, `B ⊗_ℤ ℤ̂ = B ⊗_ℚ (ℚ ⊗_ℤ ℤ̂)`, which
is `B ⊗_ℚ 𝔸_f` for `𝔸_f = ℚ ⊗_ℤ ℤ̂`.

A `ℤ`-basis `(b_k)` of `O` gives the bijection `(z_k) ↦ ∑_k b_k z_k`, `ℤ̂^κ → lim_N O/NO`, since
`O/NO` is free over `ℤ/Nℤ` with the basis `(b_k)`, and every element of `B ⊗_ℤ ℤ̂` is of the form
`∑_k (b_k / n) ⊗ z_k`, for a positive integer `n`, with image `(∑_k b_k z_k) / n` in `B̂`.

## Main definitions

* `ProfiniteIntegers`: the ring `ℤ̂`, Tau Ceti's `Additive zHat`.
* `Subalgebra.zmodToQuotient`: the ring homomorphism `ℤ/Nℤ → O/NO`.
* `Subalgebra.zHatToCompletedOrder`: the ring homomorphism `ℤ̂ → Ô`, with central image.
* `Subalgebra.zHatToFiniteAdelicAlgebra`: the ring homomorphism `ℤ̂ → B̂`.
* `Subalgebra.coordsToCompletedOrder`: the map `(z_k) ↦ ∑_k b_k z_k`, `ℤ̂^κ → Ô`.
* `Subalgebra.completedUnitsEquivUnits`: the group `Ô^× = lim_N (O/NO)^×` is the unit group of
  `Ô = lim_N O/NO`.
* `Subalgebra.tensorZHatToFiniteAdelicAlgebra`: the ring homomorphism `B ⊗_ℤ ℤ̂ → B̂`.
* `Subalgebra.tensorZHatEquivFiniteAdelicAlgebra` (LMFDB `shimcurve`): the ring isomorphism
  `B ⊗_ℤ ℤ̂ ≃ B̂`.
* `Subalgebra.tensorAdelesEquivFiniteAdelicAlgebra` (LMFDB `shimcurve`): the ring isomorphism
  `B ⊗_ℚ 𝔸_f ≃ B̂`, for `𝔸_f = ℚ ⊗_ℤ ℤ̂`.
* `Subalgebra.orderTensorZHatToTensorZHat`: the map `O ⊗_ℤ ℤ̂ → B ⊗_ℤ ℤ̂`.

## Main results

* `Subalgebra.coordsToCompletedOrder_injective`, `Subalgebra.coordsToCompletedOrder_surjective`,
  `Subalgebra.coordsToCompletedOrder_bijective`: `(z_k) ↦ ∑_k b_k z_k` is a bijection `ℤ̂^κ → Ô`.
* `Subalgebra.tensorZHatToFiniteAdelicAlgebra_bijective`: `B ⊗_ℤ ℤ̂ → B̂` is bijective.
* `Subalgebra.tensorZHatEquivFiniteAdelicAlgebra_tmul`: the isomorphism sends `x ⊗ z` to `x z`, so
  it is compatible with the embeddings of `B`.
* `Subalgebra.mem_completedOrderSubalgebra_iff_exists_tensor`: it carries the image of `O ⊗_ℤ ℤ̂`
  onto `Ô`.
-/

open Algebra Module OreLocalization TauCeti TensorProduct

open scoped TensorProduct

/-- The ring **`ℤ̂`** of profinite integers, Tau Ceti's `Additive zHat`. -/
abbrev ProfiniteIntegers : Type :=
  Additive zHat.{0}

local notation "ℤ̂" => ProfiniteIntegers

namespace Subalgebra

variable {B : Type*} [Ring B] (O : Subalgebra ℤ B)

private lemma natCast_eq_zero_quotient (N : ℕ+) :
    (((N : ℕ) : O ⧸ Ideal.span {((N : ℕ) : O)})) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : O)})),
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- The ring homomorphism `ℤ/Nℤ → O/NO`. -/
noncomputable def zmodToQuotient (N : ℕ+) : ZMod N →+* O ⧸ Ideal.span {((N : ℕ) : O)} :=
  ZMod.castHom (ringChar.dvd (natCast_eq_zero_quotient O N)) _

private lemma factor_comp_zmodToQuotient {M N : ℕ+} (h : (M : ℕ) ∣ N) :
    (Ideal.Quotient.factor (O.span_natCast_le_of_dvd h)).comp (O.zmodToQuotient N) =
      (O.zmodToQuotient M).comp (ZMod.castHom h (ZMod M)) :=
  RingHom.ext_zmod _ _

/-- The ring homomorphism **`ℤ̂ → Ô = lim_N O/NO`**, compatible with the reductions modulo `N`. -/
noncomputable def zHatToCompletedOrder : ℤ̂ →+* O.completedOrder :=
  (RingHom.pi fun N ↦ (O.zmodToQuotient N).comp (zHat.toZMod N)).codRestrict _ fun z M N h ↦ by
    have h₁ : ZMod.castHom h (ZMod M) (zHat.toZMod N z) = zHat.toZMod M z :=
      RingHom.congr_fun (zHat.castHom_comp_toZMod h) z
    have h₂ : (Ideal.Quotient.factor (O.span_natCast_le_of_dvd h)) (O.zmodToQuotient N
        (zHat.toZMod N z)) = O.zmodToQuotient M (ZMod.castHom h (ZMod M) (zHat.toZMod N z)) :=
      RingHom.congr_fun (factor_comp_zmodToQuotient O h) (zHat.toZMod N z)
    rw [h₁] at h₂
    exact h₂

private lemma commute_zmodToQuotient (N : ℕ+) (r : ZMod N) (y : O ⧸ Ideal.span {((N : ℕ) : O)}) :
    Commute (O.zmodToQuotient N r) y := by
  rw [← ZMod.natCast_zmod_val r, map_natCast]
  exact Nat.cast_commute _ y

lemma commute_zHatToCompletedOrder (z : ℤ̂) (c : O.completedOrder) :
    Commute (O.zHatToCompletedOrder z) c :=
  Subtype.ext <| funext fun N ↦ (commute_zmodToQuotient O N _ (c.1 N)).eq

/-- The ring homomorphism **`ℤ̂ → B̂`**, with central image. -/
noncomputable def zHatToFiniteAdelicAlgebra : ℤ̂ →+* O.FiniteAdelicAlgebra :=
  numeratorRingHom.comp O.zHatToCompletedOrder

lemma commute_zHatToFiniteAdelicAlgebra (z : ℤ̂) (y : O.FiniteAdelicAlgebra) :
    Commute (O.zHatToFiniteAdelicAlgebra z) y := by
  induction y using OreLocalization.ind with | c r s => ?_
  have h₁ : (O.zHatToCompletedOrder z /ₒ (1 : O.completedOrderPosNat)) * (r /ₒ s) =
      (O.zHatToCompletedOrder z * r) /ₒ s := by
    rw [oreDiv_mul_char _ r 1 s (O.zHatToCompletedOrder z) s
      (O.commute_completedOrderPosNat s _).eq, mul_one]
  have h₂ : (r /ₒ s) * (O.zHatToCompletedOrder z /ₒ (1 : O.completedOrderPosNat)) =
      (r * O.zHatToCompletedOrder z) /ₒ s :=
    mul_div_one
  have h₃ : O.zHatToCompletedOrder z * r = r * O.zHatToCompletedOrder z :=
    (O.commute_zHatToCompletedOrder z r).eq
  exact h₁.trans (h₃ ▸ h₂.symm)

variable {O} {κ : Type*} (b : Basis κ ℤ (toSubmodule O))

/-- The element `b_k` of a `ℤ`-basis of `O`, as an element of `O`. -/
private noncomputable def basisElt (k : κ) : O :=
  ⟨b k, (b k).2⟩

private lemma repr_mul_natCast (N : ℕ) (y : O) (k : κ) :
    b.repr ⟨(y * (N : O) : O), (y * (N : O)).2⟩ k = N * b.repr ⟨y, y.2⟩ k := by
  have h : (⟨(y * (N : O) : O), (y * (N : O)).2⟩ : toSubmodule O) = N • ⟨y, y.2⟩ :=
    Subtype.ext <| by
      simp [Nat.cast_comm]
  rw [h, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

private lemma dvd_repr_of_mk_eq_zero {N : ℕ+} {x : O}
    (hx : Ideal.Quotient.mk (Ideal.span {((N : ℕ) : O)}) x = 0) (k : κ) :
    ((N : ℕ) : ℤ) ∣ b.repr ⟨x, x.2⟩ k := by
  rcases Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx) with ⟨y, rfl⟩
  exact ⟨_, repr_mul_natCast b N y k⟩

private lemma zmodCast_repr_eq_of_mk_eq {M : ℕ+} {x y : O}
    (h : Ideal.Quotient.mk (Ideal.span {((M : ℕ) : O)}) x = Ideal.Quotient.mk _ y) (k : κ) :
    ((b.repr ⟨x, x.2⟩ k : ℤ) : ZMod M) = (b.repr ⟨y, y.2⟩ k : ℤ) := by
  have h₀ : Ideal.Quotient.mk (Ideal.span {((M : ℕ) : O)}) (x - y) = 0 := by
    rw [map_sub, h, sub_self]
  have h₁ : ((b.repr ⟨(x - y : O), (x - y).2⟩ k : ℤ) : ZMod M) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_repr_of_mk_eq_zero b h₀ k)
  have h₂ : (⟨(x - y : O), (x - y).2⟩ : toSubmodule O) = ⟨x, x.2⟩ - ⟨y, y.2⟩ :=
    rfl
  rw [h₂, map_sub, Finsupp.sub_apply, Int.cast_sub, sub_eq_zero] at h₁
  exact h₁

variable [Fintype κ]

private lemma eq_sum_basisElt (x : O) : x = ∑ k, b.repr ⟨x, x.2⟩ k • basisElt b k :=
  Subtype.ext <| by
    have h : ∑ k, ((b.repr ⟨x, x.2⟩ k • b k : toSubmodule O) : B) = x :=
      (AddSubmonoidClass.coe_finsetSum _ _).symm.trans (congrArg Subtype.val (b.sum_repr ⟨x, x.2⟩))
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h.symm

private lemma mk_eq_sum (N : ℕ+) (x : O) : Ideal.Quotient.mk (Ideal.span {((N : ℕ) : O)}) x =
    ∑ k, O.zmodToQuotient N (b.repr ⟨x, x.2⟩ k : ZMod N) *
      Ideal.Quotient.mk _ (basisElt b k) := by
  conv_lhs => rw [eq_sum_basisElt b x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [zsmul_eq_mul, map_mul, map_intCast, map_intCast]

/-- The map **`(z_k) ↦ ∑_k b_k z_k`** from `ℤ̂^κ` to `Ô = lim_N O/NO`, for a `ℤ`-basis `(b_k)` of
`O`. -/
noncomputable def coordsToCompletedOrder (z : κ → ℤ̂) : O.completedOrder :=
  ∑ k, O.toCompletedOrder (basisElt b k) * O.zHatToCompletedOrder (z k)

private lemma coordsToCompletedOrder_apply (N : ℕ+) (z : κ → ℤ̂) :
    (coordsToCompletedOrder b z).1 N =
      ∑ k, O.zmodToQuotient N (zHat.toZMod N (z k)) * Ideal.Quotient.mk _ (basisElt b k) := by
  rw [coordsToCompletedOrder, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ (commute_zmodToQuotient O N _ _).eq.symm

private lemma coordsToCompletedOrder_eq_zero {z : κ → ℤ̂} (hz : coordsToCompletedOrder b z = 0) :
    z = 0 := by
  refine funext fun k ↦ zHat.ext_of_toZMod fun N ↦ ?_
  let r : κ → ℤ := fun k ↦ ((zHat.toZMod N (z k)).val : ℤ)
  have hr (k : κ) : (r k : ZMod N) = zHat.toZMod N (z k) := by
    simp [r]
  let x : O := ∑ k, r k • basisElt b k
  have hxr (k : κ) : b.repr ⟨x, x.2⟩ k = r k := by
    have h : (⟨x, x.2⟩ : toSubmodule O) = ∑ k, r k • b k :=
      Subtype.ext <| by
        rw [AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]
        rfl
    rw [h, b.repr_sum_self]
  have hx : Ideal.Quotient.mk (Ideal.span {((N : ℕ) : O)}) x = 0 := by
    have h : ∑ k, O.zmodToQuotient N (zHat.toZMod N (z k)) *
        Ideal.Quotient.mk (Ideal.span {((N : ℕ) : O)}) (basisElt b k) = 0 := by
      rw [← coordsToCompletedOrder_apply, hz]
      rfl
    rw [mk_eq_sum b, ← h]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hxr, hr]
  have h₁ : (r k : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hxr k ▸ dvd_repr_of_mk_eq_zero b hx k)
  rw [← hr, h₁, Pi.zero_apply, map_zero]

lemma coordsToCompletedOrder_sub (z w : κ → ℤ̂) : coordsToCompletedOrder b (z - w) =
    coordsToCompletedOrder b z - coordsToCompletedOrder b w := by
  simp only [coordsToCompletedOrder, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

/-- **The map `(z_k) ↦ ∑_k b_k z_k`, `ℤ̂^κ → Ô`, is injective**: `O/NO` is free over `ℤ/Nℤ` with the
basis `(b_k)`. -/
lemma coordsToCompletedOrder_injective : Function.Injective (coordsToCompletedOrder b) := by
  intro z w h
  exact sub_eq_zero.mp <| coordsToCompletedOrder_eq_zero b <| by
    rw [coordsToCompletedOrder_sub, h, sub_self]

/-- **The map `(z_k) ↦ ∑_k b_k z_k`, `ℤ̂^κ → Ô`, is surjective**: the coordinates of the
representatives in `O` of a compatible family in `∏_N O/NO` are compatible, modulo `N`. -/
lemma coordsToCompletedOrder_surjective : Function.Surjective (coordsToCompletedOrder b) := by
  intro c
  choose x hx using fun N : ℕ+ ↦ Ideal.Quotient.mk_surjective (c.1 N)
  have hcomp (k : κ) (M N : ℕ+) (h : (M : ℕ) ∣ N) :
      ZMod.castHom h (ZMod M) ((b.repr ⟨x N, (x N).2⟩ k : ℤ) : ZMod N) =
        (b.repr ⟨x M, (x M).2⟩ k : ℤ) := by
    rw [map_intCast]
    refine zmodCast_repr_eq_of_mk_eq b ?_ k
    rw [hx M, ← c.2 M N h, ← hx N]
    rfl
  choose z hz using fun k ↦ (zHat.existsUnique_forall_toZMod_eq.{0} _ (hcomp k)).exists
  refine ⟨z, Subtype.ext <| funext fun N ↦ (coordsToCompletedOrder_apply b N z).trans ?_⟩
  simp only [hz]
  exact (mk_eq_sum b N (x N)).symm.trans (hx N)

/-- **The map `(z_k) ↦ ∑_k b_k z_k` is a bijection `ℤ̂^κ → Ô = lim_N O/NO`**, for a `ℤ`-basis
`(b_k)` of `O`: this is `O ⊗_ℤ ℤ̂ = lim_N O/NO`. -/
lemma coordsToCompletedOrder_bijective : Function.Bijective (coordsToCompletedOrder b) :=
  ⟨coordsToCompletedOrder_injective b, coordsToCompletedOrder_surjective b⟩

variable (O) in
/-- The families of units of the `O/NO` given by a unit of `Ô = lim_N O/NO`. -/
private noncomputable def unitsToCompletedUnits : O.completedOrderˣ →* O.completedUnits where
  toFun u := ⟨fun N ↦ ⟨u.1.1 N, u.2.1 N, congrFun (congrArg Subtype.val u.3) N,
    congrFun (congrArg Subtype.val u.4) N⟩, fun M N h ↦ Units.ext (u.1.2 M N h)⟩
  map_one' := Subtype.ext <| funext fun _ ↦ Units.ext rfl
  map_mul' _ _ := Subtype.ext <| funext fun _ ↦ Units.ext rfl

variable (O) in
/-- **The group `Ô^× = lim_N (O/NO)^×` of the LMFDB (`Subalgebra.completedUnits`) is the unit group
of the ring `Ô = lim_N O/NO`** (`Subalgebra.completedOrder`). -/
noncomputable def completedUnitsEquivUnits : O.completedUnits ≃* O.completedOrderˣ where
  toFun := O.completedUnitsToCompletedOrder.toHomUnits
  invFun := unitsToCompletedUnits O
  left_inv _ := Subtype.ext <| funext fun _ ↦ Units.ext rfl
  right_inv _ := Units.ext rfl
  map_mul' := map_mul _

private lemma sum_oreDiv (s : O.completedOrderPosNat) (r : κ → O.completedOrder) :
    ∑ k, (r k /ₒ s) = (∑ k, r k) /ₒ s := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
    exact add_oreDiv

variable [Algebra ℚ B]

/-- The element `∑_k (b_k / n) ⊗ z_k` of `B ⊗_ℤ ℤ̂`. -/
private noncomputable def tensorSum (n : ℕ) (z : κ → ℤ̂) : B ⊗[ℤ] ℤ̂ :=
  ∑ k, ((n : ℚ)⁻¹ • (b k : B)) ⊗ₜ[ℤ] z k

private lemma natCast_mul_inv_smul {n : ℕ} (hn : n ≠ 0) (x : B) :
    (n : B) * ((n : ℚ)⁻¹ • x) = x := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

private lemma natCast_smul_mul_inv_smul {n n' : ℕ} (hn' : n' ≠ 0) (x : B) :
    (n' : ℤ) • (((n * n' : ℕ) : ℚ)⁻¹ • x) = (n : ℚ)⁻¹ • x := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, Nat.cast_mul, mul_inv, mul_comm,
    mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn'), mul_one]

private lemma exists_eq_tensorSum (hO : O.IsQuaternionOrder) (t : B ⊗[ℤ] ℤ̂) :
    ∃ (n : ℕ) (_ : n ≠ 0) (z : κ → ℤ̂), t = tensorSum b n z := by
  induction t using TensorProduct.inductionOn with
  | tmul x w =>
    rcases O.exists_natCast_mul_mem hO x with ⟨n, hn, hnx⟩
    refine ⟨n, hn, fun k ↦ b.repr ⟨_, hnx⟩ k • w, ?_⟩
    have h₁ : (n : B) * x = ∑ k, b.repr ⟨_, hnx⟩ k • (b k : B) :=
      (congrArg Subtype.val (b.sum_repr ⟨_, hnx⟩)).symm.trans (AddSubmonoidClass.coe_finsetSum _ _)
    have h₂ : x = (n : ℚ)⁻¹ • ((n : B) * x) := by
      rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]
    rw [h₁, Finset.smul_sum] at h₂
    have h : x = ∑ k, b.repr ⟨_, hnx⟩ k • ((n : ℚ)⁻¹ • (b k : B)) :=
      h₂.trans (Finset.sum_congr rfl fun k _ ↦ smul_comm _ _ _)
    rw [tensorSum]
    conv_lhs => rw [h]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun k _ ↦ TensorProduct.smul_tmul _ _ _
  | add t t' ht ht' =>
    rcases ht with ⟨n, hn, z, rfl⟩
    rcases ht' with ⟨n', hn', z', rfl⟩
    refine ⟨n * n', mul_ne_zero hn hn', fun k ↦ (n' : ℤ) • z k + (n : ℤ) • z' k, ?_⟩
    simp only [tensorSum, TensorProduct.tmul_add, Finset.sum_add_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ ↦ ?_
    · rw [← TensorProduct.smul_tmul, natCast_smul_mul_inv_smul hn']
    · rw [← TensorProduct.smul_tmul, mul_comm n n', natCast_smul_mul_inv_smul hn]

private lemma eq_zero_of_oreDiv_eq_zero {c : O.completedOrder} {s : O.completedOrderPosNat}
    (h : c /ₒ s = 0) : c = 0 := by
  rw [OreLocalization.zero_def, oreDiv_eq_iff] at h
  rcases h with ⟨⟨_, k, hk, rfl⟩, v, h₁, h₂⟩
  rw [Submonoid.smul_def, smul_eq_mul, smul_eq_mul, mul_zero] at h₁
  have h₃ : (k : O.completedOrder) = v * s := by
    simpa using h₂
  refine O.eq_zero_of_natCast_mul_eq_zero (nonZeroDivisors.ne_zero hk) ?_
  rw [h₃, mul_assoc, (O.commute_completedOrderPosNat s c).eq, ← mul_assoc, ← h₁, zero_mul]

variable (hO : O.IsQuaternionOrder)

/-- The ring homomorphism **`B ⊗_ℤ ℤ̂ → B̂`**, `x ⊗ z ↦ x z`. -/
noncomputable def tensorZHatToFiniteAdelicAlgebra : B ⊗[ℤ] ℤ̂ →+* O.FiniteAdelicAlgebra :=
  letI : Algebra ℤ O.FiniteAdelicAlgebra := Ring.toIntAlgebra O.FiniteAdelicAlgebra
  (lift (RingHom.toIntAlgHom (S := O.FiniteAdelicAlgebra) (O.toFiniteAdelicAlgebra hO))
    (RingHom.toIntAlgHom (S := O.FiniteAdelicAlgebra) O.zHatToFiniteAdelicAlgebra) fun _ z ↦
      (O.commute_zHatToFiniteAdelicAlgebra z _).symm).toRingHom

lemma tensorZHatToFiniteAdelicAlgebra_tmul (x : B) (z : ℤ̂) :
    tensorZHatToFiniteAdelicAlgebra hO (x ⊗ₜ z) =
      O.toFiniteAdelicAlgebra hO x * O.zHatToFiniteAdelicAlgebra z := by
  let _ : Algebra ℤ O.FiniteAdelicAlgebra := Ring.toIntAlgebra O.FiniteAdelicAlgebra
  exact lift_tmul ..

private lemma toFiniteAdelicAlgebra_inv_smul {n : ℕ} (hn : n ≠ 0) {x : B} (hx : x ∈ O) :
    O.toFiniteAdelicAlgebra hO ((n : ℚ)⁻¹ • x) = O.toCompletedOrder ⟨x, hx⟩ /ₒ O.natDenom hn := by
  have h : (n : B) * ((n : ℚ)⁻¹ • x) ∈ O := by
    rwa [natCast_mul_inv_smul hn]
  rw [toFiniteAdelicAlgebra_apply, O.toFiniteAdelicAlgebraFun_eq hn hO h]
  exact congrArg (· /ₒ O.natDenom hn) (congrArg O.toCompletedOrder
    (Subtype.ext (natCast_mul_inv_smul hn _)))

private lemma tensorZHatToFiniteAdelicAlgebra_tensorSum {n : ℕ} (hn : n ≠ 0) (z : κ → ℤ̂) :
    tensorZHatToFiniteAdelicAlgebra hO (tensorSum b n z) =
      coordsToCompletedOrder b z /ₒ O.natDenom hn := by
  rw [tensorSum, map_sum, coordsToCompletedOrder, ← sum_oreDiv]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [tensorZHatToFiniteAdelicAlgebra_tmul, toFiniteAdelicAlgebra_inv_smul hO hn (b k).2,
    zHatToFiniteAdelicAlgebra, RingHom.comp_apply, numeratorRingHom_apply, mul_div_one]
  rfl

/-- **`x ⊗ z ↦ x z` is a bijection `B ⊗_ℤ ℤ̂ → B̂`**, for an order `O` of a quaternion algebra `B`
over `ℚ`: a `ℤ`-basis `(b_k)` of `O` writes every element of `B ⊗_ℤ ℤ̂` as `∑_k (b_k / n) ⊗ z_k`,
with image `(∑_k b_k z_k) / n`, and `Ô = lim_N O/NO` has no torsion. -/
lemma tensorZHatToFiniteAdelicAlgebra_bijective :
    Function.Bijective (tensorZHatToFiniteAdelicAlgebra hO) := by
  have : Submodule.IsLattice ℚ (toSubmodule O) := hO
  let c : Basis (Free.ChooseBasisIndex ℤ (toSubmodule O)) ℤ (toSubmodule O) :=
    Free.chooseBasis ℤ (toSubmodule O)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_, fun y ↦ ?_⟩
  · rcases exists_eq_tensorSum c hO t with ⟨n, hn, z, rfl⟩
    rw [tensorZHatToFiniteAdelicAlgebra_tensorSum c hO hn] at ht
    have hz : z = 0 := coordsToCompletedOrder_eq_zero c (eq_zero_of_oreDiv_eq_zero ht)
    simp [tensorSum, hz]
  · induction y using OreLocalization.ind with | c r s => ?_
    rcases s with ⟨_, n, hn, rfl⟩
    rcases coordsToCompletedOrder_surjective c r with ⟨z, rfl⟩
    exact ⟨tensorSum c n z, tensorZHatToFiniteAdelicAlgebra_tensorSum c hO
      (nonZeroDivisors.ne_zero hn) z⟩

/-- The **ring isomorphism `B ⊗_ℤ ℤ̂ ≃ B̂`** (LMFDB `shimcurve`), `x ⊗ z ↦ x z`, for an order `O` of
a quaternion algebra `B` over `ℚ`, between the ring `B̂ = B ⊗_ℤ ℤ̂` of the knowl and the model
`Ô[1/n : n ≥ 1]` of `Subalgebra.FiniteAdelicAlgebra`. -/
noncomputable def tensorZHatEquivFiniteAdelicAlgebra : B ⊗[ℤ] ℤ̂ ≃+* O.FiniteAdelicAlgebra :=
  RingEquiv.ofBijective _ (tensorZHatToFiniteAdelicAlgebra_bijective hO)

/-- The **ring isomorphism `B ⊗_ℚ (ℚ ⊗_ℤ ℤ̂) ≃ B̂`** with the ring of finite adèles
`𝔸_f = ℚ ⊗_ℤ ℤ̂`, for an order `O` of a quaternion algebra `B` over `ℚ`: the comparison of the
knowl's `B ⊗_ℚ 𝔸_f` with the localization `Ô[1/n : n ≥ 1]` of `Subalgebra.FiniteAdelicAlgebra`. -/
noncomputable def tensorAdelesEquivFiniteAdelicAlgebra :
    B ⊗[ℚ] (ℚ ⊗[ℤ] ℤ̂) ≃+* O.FiniteAdelicAlgebra :=
  letI e : (B ⊗[ℤ] ℤ̂) ≃ₐ[ℚ] B ⊗[ℚ] (ℚ ⊗[ℤ] ℤ̂) :=
    AlgEquiv.ofLinearEquiv (AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ B ℤ̂).symm
      (by simp [one_def]) (LinearMap.map_mul_of_map_mul_tmul fun _ _ _ _ ↦ by simp)
  e.symm.toRingEquiv.trans (tensorZHatEquivFiniteAdelicAlgebra hO)

/-- **The isomorphism `B ⊗_ℤ ℤ̂ ≃ B̂` sends `x ⊗ z` to `x z`**, so `x ⊗ 1` to the image of `x` under
the embedding `B → B̂`. -/
lemma tensorZHatEquivFiniteAdelicAlgebra_tmul (x : B) (z : ℤ̂) :
    tensorZHatEquivFiniteAdelicAlgebra hO (x ⊗ₜ z) =
      O.toFiniteAdelicAlgebra hO x * O.zHatToFiniteAdelicAlgebra z :=
  tensorZHatToFiniteAdelicAlgebra_tmul hO x z

variable (O) in
/-- The map `O ⊗_ℤ ℤ̂ → B ⊗_ℤ ℤ̂`. -/
noncomputable def orderTensorZHatToTensorZHat : O ⊗[ℤ] ℤ̂ →ₗ[ℤ] B ⊗[ℤ] ℤ̂ :=
  TensorProduct.map O.val.toLinearMap LinearMap.id

/-- **The isomorphism `B ⊗_ℤ ℤ̂ ≃ B̂` carries the image of `O ⊗_ℤ ℤ̂` onto `Ô`** (LMFDB
`shimcurve`): `Ô = lim_N O/NO` is `O ⊗_ℤ ℤ̂`. -/
lemma mem_completedOrderSubalgebra_iff_exists_tensor (y : O.FiniteAdelicAlgebra) : y ∈
    O.completedOrderSubalgebra ↔ ∃ t : O ⊗[ℤ] ℤ̂,
      tensorZHatEquivFiniteAdelicAlgebra hO (O.orderTensorZHatToTensorZHat t) = y := by
  have : Submodule.IsLattice ℚ (toSubmodule O) := hO
  let c : Basis (Free.ChooseBasisIndex ℤ (toSubmodule O)) ℤ (toSubmodule O) :=
    Free.chooseBasis ℤ (toSubmodule O)
  refine ⟨fun hy ↦ ?_, ?_⟩
  · rcases O.mem_completedOrderSubalgebra_iff.mp hy with ⟨r, rfl⟩
    rcases coordsToCompletedOrder_surjective c r with ⟨z, rfl⟩
    refine ⟨∑ k, basisElt c k ⊗ₜ z k, ?_⟩
    rw [map_sum, map_sum, coordsToCompletedOrder, ← sum_oreDiv]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have h : O.orderTensorZHatToTensorZHat (basisElt c k ⊗ₜ[ℤ] z k) = (c k : B) ⊗ₜ[ℤ] z k :=
      rfl
    rw [h, tensorZHatEquivFiniteAdelicAlgebra_tmul, O.toFiniteAdelicAlgebra_apply hO,
      O.toFiniteAdelicAlgebraFun_of_mem hO (c k).2, zHatToFiniteAdelicAlgebra, RingHom.comp_apply,
      numeratorRingHom_apply, mul_div_one]
    rfl
  · rintro ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul x z =>
      have h : O.orderTensorZHatToTensorZHat (x ⊗ₜ[ℤ] z) = (x : B) ⊗ₜ[ℤ] z :=
        rfl
      rw [h, tensorZHatEquivFiniteAdelicAlgebra_tmul]
      exact mul_mem (O.toFiniteAdelicAlgebra_mem hO x.2)
        (O.mem_completedOrderSubalgebra_iff.mpr ⟨_, rfl⟩)
    | add t t' ht ht' =>
      rw [map_add, map_add]
      exact add_mem ht ht'

end Subalgebra
