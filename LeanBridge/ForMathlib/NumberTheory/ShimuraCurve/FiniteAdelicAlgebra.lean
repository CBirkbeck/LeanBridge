import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroup
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrder
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# The finite adelic algebra `B̂ = B ⊗ 𝔸_f` of a quaternion algebra

Let `O` be an order of a quaternion algebra `B` over `ℚ`. As in
`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroup`, where `Ô^×` is the inverse limit
`lim_N (O/NO)^×`, the ring `Ô = O ⊗ ℤ̂` is the inverse limit `lim_N O/NO`, the compatible families
`(x_N)_N ∈ ∏_N O/NO` over the positive integers `N`, and `B̂ = B ⊗_ℤ ℤ̂ = B ⊗_ℚ 𝔸_f` (LMFDB
`shimcurve`) is `Ô ⊗ ℚ`, the localization `Ô[1/n : n ≥ 1]` of `Ô` at the positive integers, which
are central: these agree with the tensor products since `O` is free of finite rank over `ℤ` and
`𝔸_f = ℤ̂ ⊗ ℚ`. The localization is Mathlib's Ore localization. A `ℤ`-basis of `O` being a
`ℚ`-basis of `B`, every `x ∈ B` has a multiple `n x ∈ O`, `n ≥ 1`, and `x ↦ (n x) / n` is the
embedding `B → B̂`.

The two facts which make `Ô` and `B̂` the expected objects are proved: every element of `B̂` has a
multiple in `Ô` by a positive integer, and `B ∩ Ô = O`, that is, an element of `B` whose image lies
in `Ô` lies in `O`. Conjugation by an element of the normalizer `N_{B^×}(O)` acts on `Ô`
componentwise, and agrees there with the conjugation in `B̂`.

## Main definitions

* `Subalgebra.completedOrder` (LMFDB `shimcurve`): the ring `Ô = lim_N O/NO`.
* `Subalgebra.toCompletedOrder`: the diagonal embedding `O → Ô`.
* `Subalgebra.FiniteAdelicAlgebra` (LMFDB `shimcurve`): the ring `B̂ = Ô[1/n : n ≥ 1]`.
* `Subalgebra.completedOrderSubalgebra`: the subring `Ô` of `B̂`.
* `Subalgebra.completedOrderNormalizer`: the normalizer of `Ô` in `B̂^×`.
* `Subalgebra.completedUnitsToUnits`: the embedding `Ô^× → B̂^×`.
* `Subalgebra.completedOrderConj`: conjugation by an element of `N_{B^×}(O)` on `Ô`.
* `Subalgebra.toFiniteAdelicAlgebra` (LMFDB `shimcurve`): the embedding `B → B̂`.

## Main results

* `Subalgebra.exists_natCast_mul_mem_completedOrderSubalgebra`: every element of `B̂` has a multiple
  in `Ô` by a positive integer.
* `Subalgebra.mem_of_toFiniteAdelicAlgebra_mem` (LMFDB `shimcurve`): `B ∩ Ô = O`.
* `Subalgebra.oreDiv_mul_toFiniteAdelicAlgebra`: conjugation by `γ ∈ N_{B^×}(O)` in `B̂` preserves
  `Ô`, where it is the componentwise conjugation.
-/

open OreLocalization

namespace Subalgebra

variable {B : Type*} [Ring B] (O : Subalgebra ℤ B)

/-- The ring **`Ô = O ⊗ ℤ̂`** (LMFDB `shimcurve`) of a subring `O` of `B`, as the inverse limit
`lim_N O/NO`: the families `(x_N)_N ∈ ∏_N O/NO` over the positive integers `N` such that `x_N`
reduces to `x_M` modulo `M` whenever `M ∣ N`. Its units are `Subalgebra.completedUnits`. -/
def completedOrder : Subring (∀ N : ℕ+, O ⧸ Ideal.span {((N : ℕ) : O)}) where
  carrier := {x | ∀ M N : ℕ+, ∀ h : (M : ℕ) ∣ N,
    Ideal.Quotient.factor (O.span_natCast_le_of_dvd h) (x N) = x M}
  mul_mem' hx hy M N h := by
    rw [Pi.mul_apply, map_mul, hx M N h, hy M N h, Pi.mul_apply]
  one_mem' _ _ _ := map_one _
  add_mem' hx hy M N h := by
    rw [Pi.add_apply, map_add, hx M N h, hy M N h, Pi.add_apply]
  zero_mem' _ _ _ := map_zero _
  neg_mem' hx M N h := by
    rw [Pi.neg_apply, map_neg, hx M N h, Pi.neg_apply]

/-- The diagonal embedding `O → Ô = lim_N O/NO`, sending `x` to the family of its reductions. -/
def toCompletedOrder : O →+* O.completedOrder :=
  (RingHom.pi fun _ ↦ Ideal.Quotient.mk _).codRestrict _ fun _ _ _ _ ↦ rfl

/-- The positive integers in `Ô`, a central submonoid. -/
def completedOrderPosNat : Submonoid O.completedOrder :=
  (nonZeroDivisors ℕ).map (Nat.castRingHom O.completedOrder)

lemma commute_completedOrderPosNat (s : O.completedOrderPosNat) (r : O.completedOrder) :
    Commute (s : O.completedOrder) r := by
  rcases s.2 with ⟨n, -, hn⟩
  rw [← hn]
  exact Nat.cast_commute n r

instance : OreSet O.completedOrderPosNat where
  ore_right_cancel r₁ r₂ s h :=
    ⟨s, ((O.commute_completedOrderPosNat s r₁).eq.trans h).trans (O.commute_completedOrderPosNat s
      r₂).eq.symm⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := (O.commute_completedOrderPosNat s r).eq

/-- The ring **`B̂ = B ⊗_ℚ 𝔸_f`** (LMFDB `shimcurve`) of finite adelic points of `B`, for an order
`O` of `B`, as `Ô ⊗ ℚ`: the localization `Ô[1/n : n ≥ 1]` of `Ô = lim_N O/NO` at the positive
integers, which are central. -/
abbrev FiniteAdelicAlgebra : Type _ :=
  OreLocalization O.completedOrderPosNat O.completedOrder

variable {n : ℕ} (hn : n ≠ 0)

/-- The positive integer `n` as a denominator in `B̂`. -/
def natDenom : O.completedOrderPosNat :=
  ⟨n, n, mem_nonZeroDivisors_of_ne_zero hn, rfl⟩

@[simp]
lemma coe_natDenom : (O.natDenom hn : O.completedOrder) = n :=
  rfl

/-- The subring **`Ô`** of `B̂`: the fractions `x / 1`, `x ∈ Ô`. -/
noncomputable def completedOrderSubalgebra :=
  (numeratorRingHom (R := O.completedOrder) (S := O.completedOrderPosNat)).rangeS

lemma mem_completedOrderSubalgebra_iff {y : O.FiniteAdelicAlgebra} :
    y ∈ O.completedOrderSubalgebra ↔ ∃ c : O.completedOrder, c /ₒ 1 = y :=
  RingHom.mem_rangeS

/-- The normalizer `N_{B̂^×}(Ô) = {u ∈ B̂^× : u Ô u⁻¹ = Ô}` of `Ô` in `B̂^×`. -/
def completedOrderNormalizer : Subgroup O.FiniteAdelicAlgebraˣ where
  carrier := {u | ∀ y, y ∈ O.completedOrderSubalgebra ↔
    (u : O.FiniteAdelicAlgebra) * y * ↑u⁻¹ ∈ O.completedOrderSubalgebra}
  one_mem' y := by
    simp
  mul_mem' {u v} hu hv y := by
    rw [hv, hu]
    simp [mul_assoc]
  inv_mem' {u} hu y := by
    simpa [mul_assoc] using (hu (↑u⁻¹ * y * u)).symm

/-- **Every element of `B̂` has a multiple in `Ô` by a positive integer.** -/
lemma exists_natCast_mul_mem_completedOrderSubalgebra (y : O.FiniteAdelicAlgebra) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : O.FiniteAdelicAlgebra) * y ∈ O.completedOrderSubalgebra := by
  induction y using OreLocalization.ind with | c r s => ?_
  rcases s with ⟨_, n, hn, rfl⟩
  refine ⟨n, nonZeroDivisors.ne_zero hn, O.mem_completedOrderSubalgebra_iff.mpr ⟨r, ?_⟩⟩
  rw [← map_natCast numeratorRingHom]
  exact OreLocalization.mul_cancel.symm

lemma toCompletedOrder_oreDiv_eq {x : B} {m : ℕ} (hm : m ≠ 0) (hmx : (m : B) * x ∈ O)
    (hnx : (n : B) * x ∈ O) : O.toCompletedOrder ⟨_, hmx⟩ /ₒ O.natDenom hm =
    O.toCompletedOrder ⟨_, hnx⟩ /ₒ O.natDenom hn := by
  rw [oreDiv_eq_iff]
  refine ⟨O.natDenom hm, n, ?_, Nat.cast_comm m (n : O.completedOrder)⟩
  rw [Submonoid.smul_def, smul_eq_mul, smul_eq_mul, coe_natDenom,
    ← map_natCast O.toCompletedOrder m, ← map_natCast O.toCompletedOrder n, ← map_mul, ← map_mul]
  refine congrArg O.toCompletedOrder <| Subtype.ext ?_
  push_cast
  rw [← mul_assoc, ← mul_assoc, Nat.cast_comm m (n : B)]

/-- The inclusion `Ô^× → Ô` of the units of `Ô = lim_N O/NO`, as the families of units of the
`O/NO`. -/
def completedUnitsToCompletedOrder : O.completedUnits →* O.completedOrder where
  toFun x := ⟨fun N ↦ (x.1 N : O ⧸ Ideal.span {((N : ℕ) : O)}), fun M N h ↦
    congrArg Units.val (x.2 M N h)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The embedding **`Ô^× → B̂^×`** of the units `Subalgebra.completedUnits` of `Ô` in the units of
`B̂`. -/
noncomputable def completedUnitsToUnits : O.completedUnits →* O.FiniteAdelicAlgebraˣ :=
  (Units.map numeratorHom).comp O.completedUnitsToCompletedOrder.toHomUnits

lemma mem_completedOrderNormalizer_of_forall {u : O.FiniteAdelicAlgebraˣ}
    (h₁ : ∀ y ∈ O.completedOrderSubalgebra, ↑u * y * ↑u⁻¹ ∈ O.completedOrderSubalgebra)
    (h₂ : ∀ y ∈ O.completedOrderSubalgebra, ↑u⁻¹ * y * ↑u ∈ O.completedOrderSubalgebra) :
    u ∈ O.completedOrderNormalizer :=
  fun y ↦ ⟨h₁ y, fun h ↦ by simpa [mul_assoc] using h₂ _ h⟩

lemma completedUnitsToUnits_mem_completedOrderNormalizer (x : O.completedUnits) :
    O.completedUnitsToUnits x ∈ O.completedOrderNormalizer := by
  have h₁ : (O.completedUnitsToUnits x : O.FiniteAdelicAlgebra) ∈ O.completedOrderSubalgebra :=
    O.mem_completedOrderSubalgebra_iff.mpr ⟨_, rfl⟩
  have h₂ : (↑(O.completedUnitsToUnits x)⁻¹ : O.FiniteAdelicAlgebra) ∈
      O.completedOrderSubalgebra :=
    O.mem_completedOrderSubalgebra_iff.mpr ⟨O.completedUnitsToCompletedOrder x⁻¹, rfl⟩
  exact O.mem_completedOrderNormalizer_of_forall (fun _ hy ↦ mul_mem (mul_mem h₁ hy) h₂)
    fun _ hy ↦ mul_mem (mul_mem h₂ hy) h₁

variable (γ : O.unitsNormalizer) (c : O.completedOrder)

lemma span_natCast_le_comap_unitsNormalizerConj (N : ℕ) :
    Ideal.span {(N : O)} ≤ (Ideal.span {(N : O)}).comap (O.unitsNormalizerConj γ).toRingHom := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    RingEquiv.toRingHom_eq_coe, map_natCast]
  exact Ideal.mem_span_singleton_self _

/-- Conjugation `x ↦ γ x γ⁻¹` by an element `γ` of the normalizer `N_{B^×}(O)` on
`Ô = lim_N O/NO`, componentwise on the `O/NO`, which `γ` preserves. -/
noncomputable def completedOrderConj : O.completedOrder →+* O.completedOrder :=
  ((RingHom.pi fun N : ℕ+ ↦ (Ideal.quotientMap _ _ (O.span_natCast_le_comap_unitsNormalizerConj γ
    N)).comp (Pi.evalRingHom _ N)).comp O.completedOrder.subtype).codRestrict _
      fun (c : O.completedOrder) M N h ↦ by
        rcases Ideal.Quotient.mk_surjective (c.1 N) with ⟨z, hz⟩
        have h1 : Ideal.Quotient.factor (O.span_natCast_le_of_dvd h) (Ideal.quotientMap _ _
            (O.span_natCast_le_comap_unitsNormalizerConj γ N) (c.1 N)) = Ideal.quotientMap _ _
            (O.span_natCast_le_comap_unitsNormalizerConj γ M) (c.1 M) := by
          rw [← c.2 M N h, ← hz]
          rfl
        exact h1

lemma completedOrderConj_apply (N : ℕ+) :
    (O.completedOrderConj γ c : ∀ N : ℕ+, O ⧸ Ideal.span {((N : ℕ) : O)}) N =
      Ideal.quotientMap _ _ (O.span_natCast_le_comap_unitsNormalizerConj γ N) (c.1 N) :=
  rfl

lemma completedOrderConj_mul_toCompletedOrder (hnγ : (n : B) * (γ : Bˣ) ∈ O) :
    O.completedOrderConj γ c * O.toCompletedOrder ⟨_, hnγ⟩ = O.toCompletedOrder ⟨_, hnγ⟩ * c := by
  refine Subtype.ext <| funext fun N ↦ ?_
  rcases Ideal.Quotient.mk_surjective (c.1 N) with ⟨z, hz⟩
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, Pi.mul_apply, Pi.mul_apply,
    completedOrderConj_apply, ← hz, Ideal.quotientMap_mk]
  have h : (O.unitsNormalizerConj γ).toRingHom z * ⟨_, hnγ⟩ = ⟨_, hnγ⟩ * z := Subtype.ext <| by
    simp only [MulMemClass.coe_mul, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      coe_unitsNormalizerConj_apply]
    rw [← nsmul_eq_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  exact (map_mul (Ideal.Quotient.mk _) _ _).symm.trans <| (congrArg _ h).trans (map_mul _ _ _)

variable [Algebra ℚ B]

lemma isUnit_natCast_of_ne_zero {k : ℕ} (hk : k ≠ 0) : IsUnit (k : B) := by
  rw [← map_natCast (algebraMap ℚ B)]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hk)).map _

variable {c} in
lemma eq_zero_of_natCast_mul_eq_zero {k : ℕ} (hk : k ≠ 0) (h : (k : O.completedOrder) * c = 0) :
    c = 0 := by
  refine Subtype.ext <| funext fun N ↦ ?_
  let K : ℕ+ := ⟨k, Nat.pos_of_ne_zero hk⟩
  rcases Ideal.Quotient.mk_surjective (c.1 (K * N)) with ⟨z, hz⟩
  have h1 : Ideal.Quotient.mk (Ideal.span {(((K * N : ℕ+) : ℕ) : O)}) ((k : O) * z) = 0 := by
    rw [map_mul, map_natCast, hz]
    exact congrFun (congrArg Subtype.val h) (K * N)
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
  rcases h1 with ⟨a, ha⟩
  have hz' : z = a * ((N : ℕ) : O) := by
    refine Subtype.ext <| (isUnit_natCast_of_ne_zero hk).mul_left_cancel ?_
    have ha' : (a : B) * (((K : ℕ) : B) * N) = k * z := by
      simpa using congrArg Subtype.val ha
    rw [← ha', MulMemClass.coe_mul, ← mul_assoc, ← mul_assoc, Nat.cast_comm k (a : B)]
    rfl
  rw [← c.2 N (K * N) (dvd_mul_left _ _), ← hz, hz', Ideal.Quotient.factor_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr <| Ideal.mul_mem_left _ _ <|
    Ideal.mem_span_singleton_self _

lemma exists_natCast_mul_mem (hO : O.IsQuaternionOrder) (x : B) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : B) * x ∈ O := by
  have hx : x ∈ Submodule.span ℚ (toSubmodule O : Set B) := hO.span_eq_top ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    rcases hy with ⟨m, hm, hy⟩
    rcases hz with ⟨n, hn, hz⟩
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have h : ((m * n : ℕ) : B) * (y + z) = n * (m * y) + m * (n * z) := by
      rw [Nat.cast_mul, mul_add, ← mul_assoc, ← mul_assoc, Nat.cast_comm n (m : B)]
    exact h ▸ add_mem (mul_mem (natCast_mem O n) hy) (mul_mem (natCast_mem O m) hz)
  | smul q y _ hy =>
    rcases hy with ⟨n, hn, hy⟩
    refine ⟨q.den * n, mul_ne_zero q.den_ne_zero hn, ?_⟩
    have h : ((q.den * n : ℕ) : B) * (q • y) = q.num * (n * y) := by
      rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, ← map_natCast (algebraMap ℚ B) (q.den * n),
        ← map_natCast (algebraMap ℚ B) n, ← map_intCast (algebraMap ℚ B), ← map_mul, ← map_mul]
      congr 2
      push_cast
      rw [← Rat.mul_den_eq_num q]
      ring1
    exact h ▸ mul_mem (intCast_mem O q.num) hy

variable (hO : O.IsQuaternionOrder) {x : B}

variable (x) in
/-- The function `x ↦ (n x) / n` underlying the embedding `B → B̂`, for a positive integer `n` with
`n x ∈ O`, chosen here. -/
noncomputable def toFiniteAdelicAlgebraFun : O.FiniteAdelicAlgebra :=
  O.toCompletedOrder ⟨_, (O.exists_natCast_mul_mem hO x).choose_spec.2⟩ /ₒ
    O.natDenom (O.exists_natCast_mul_mem hO x).choose_spec.1

lemma toFiniteAdelicAlgebraFun_eq (hnx : (n : B) * x ∈ O) :
    O.toFiniteAdelicAlgebraFun hO x = O.toCompletedOrder ⟨_, hnx⟩ /ₒ O.natDenom hn :=
  O.toCompletedOrder_oreDiv_eq hn _ _ hnx

lemma toFiniteAdelicAlgebraFun_of_mem (hx : x ∈ O) :
    O.toFiniteAdelicAlgebraFun hO x = O.toCompletedOrder ⟨x, hx⟩ /ₒ 1 := by
  rw [O.toFiniteAdelicAlgebraFun_eq one_ne_zero hO (by simpa using hx)]
  congr 1
  · exact congrArg O.toCompletedOrder <| Subtype.ext <| by simp
  · exact Subtype.ext Nat.cast_one

/-- The **embedding `B → B̂`** (LMFDB `shimcurve`) of a quaternion algebra `B` over `ℚ` into its
ring of finite adelic points, for an order `O` of `B`: `x ↦ (n x) / n` for any positive integer `n`
with `n x ∈ O`. -/
noncomputable def toFiniteAdelicAlgebra : B →+* O.FiniteAdelicAlgebra where
  toFun := O.toFiniteAdelicAlgebraFun hO
  map_one' := by
    rw [O.toFiniteAdelicAlgebraFun_of_mem hO O.one_mem, OreLocalization.one_def]
    exact congrArg (· /ₒ 1) (map_one O.toCompletedOrder)
  map_mul' x y := by
    rcases O.exists_natCast_mul_mem hO x with ⟨m, hm, hx⟩
    rcases O.exists_natCast_mul_mem hO y with ⟨n, hn, hy⟩
    have hxy : ((n * m : ℕ) : B) * (x * y) = m * x * (n * y) := by
      rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← nsmul_eq_mul, smul_mul_smul_comm, mul_comm m n]
    rw [O.toFiniteAdelicAlgebraFun_eq (mul_ne_zero hn hm) hO (hxy ▸ mul_mem hx hy),
      O.toFiniteAdelicAlgebraFun_eq hm hO hx, O.toFiniteAdelicAlgebraFun_eq hn hO hy,
      oreDiv_mul_oreDiv]
    congr 1
    · exact (congrArg O.toCompletedOrder (Subtype.ext hxy)).trans (map_mul _ _ _)
    · exact Subtype.ext (Nat.cast_mul n m)
  map_zero' := by
    rw [O.toFiniteAdelicAlgebraFun_of_mem hO O.zero_mem, OreLocalization.zero_def]
    exact congrArg (· /ₒ 1) (map_zero O.toCompletedOrder)
  map_add' x y := by
    rcases O.exists_natCast_mul_mem hO x with ⟨m, hm, hx⟩
    rcases O.exists_natCast_mul_mem hO y with ⟨n, hn, hy⟩
    have hx' : ((m * n : ℕ) : B) * x ∈ O := by
      rw [Nat.cast_mul, Nat.cast_comm m (n : B), mul_assoc]
      exact mul_mem (natCast_mem O n) hx
    have hy' : ((m * n : ℕ) : B) * y ∈ O := by
      rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem O m) hy
    have e (r : O.completedOrder) : r /ₒ O.natDenom (mul_ne_zero hm hn) =
        1 /ₒ O.natDenom (mul_ne_zero hm hn) * numeratorRingHom r := by
      rw [numeratorRingHom_apply, mul_div_one, one_mul]
    have hxy' : ((m * n : ℕ) : B) * (x + y) ∈ O :=
      mul_add (_ : B) x y ▸ add_mem hx' hy'
    rw [O.toFiniteAdelicAlgebraFun_eq (mul_ne_zero hm hn) hO hxy',
      O.toFiniteAdelicAlgebraFun_eq (mul_ne_zero hm hn) hO hx',
      O.toFiniteAdelicAlgebraFun_eq (mul_ne_zero hm hn) hO hy', e (O.toCompletedOrder ⟨_, hxy'⟩),
      e (O.toCompletedOrder ⟨_, hx'⟩), e (O.toCompletedOrder ⟨_, hy'⟩),
      ← OreLocalization.left_distrib]
    have h : (⟨_, hxy'⟩ : O) = ⟨_, hx'⟩ + ⟨_, hy'⟩ :=
      Subtype.ext (mul_add _ x y)
    rw [h, map_add O.toCompletedOrder, map_add numeratorRingHom]

variable (x) in
lemma toFiniteAdelicAlgebra_apply :
    O.toFiniteAdelicAlgebra hO x = O.toFiniteAdelicAlgebraFun hO x :=
  rfl

lemma toFiniteAdelicAlgebra_mem (hx : x ∈ O) :
    O.toFiniteAdelicAlgebra hO x ∈ O.completedOrderSubalgebra :=
  O.mem_completedOrderSubalgebra_iff.mpr ⟨_, (O.toFiniteAdelicAlgebraFun_of_mem hO hx).symm⟩

/-- **`B ∩ Ô = O`** (LMFDB `shimcurve`): an element `x` of `B` whose image in `B̂` lies in `Ô` lies
in `O`. If `n x ∈ O` and `(n x) / n = c / 1` with `c ∈ Ô`, then `n x = n c` in `Ô`, `Ô` having no
torsion, so `n x` vanishes modulo `n O`. -/
lemma mem_of_toFiniteAdelicAlgebra_mem
    (hx : O.toFiniteAdelicAlgebra hO x ∈ O.completedOrderSubalgebra) : x ∈ O := by
  rcases O.exists_natCast_mul_mem hO x with ⟨n, hn, hnx⟩
  rcases O.mem_completedOrderSubalgebra_iff.mp hx with ⟨c, hc⟩
  rw [toFiniteAdelicAlgebra_apply, O.toFiniteAdelicAlgebraFun_eq hn hO hnx, oreDiv_eq_iff] at hc
  rcases hc with ⟨⟨_, k, hk, rfl⟩, v, h1, h2⟩
  rw [Submonoid.smul_def, smul_eq_mul, smul_eq_mul] at h1
  have h2' : (k : O.completedOrder) * n = v :=
    h2.trans (mul_one v)
  have h3 : (k : O.completedOrder) * (O.toCompletedOrder ⟨_, hnx⟩ - n * c) = 0 := by
    rw [mul_sub, ← mul_assoc, h2']
    exact sub_eq_zero.mpr h1
  have h4 : O.toCompletedOrder ⟨_, hnx⟩ = n * c :=
    sub_eq_zero.mp (O.eq_zero_of_natCast_mul_eq_zero (nonZeroDivisors.ne_zero hk) h3)
  let N : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
  have h5 : Ideal.Quotient.mk (Ideal.span {((N : ℕ) : O)}) ⟨_, hnx⟩ = 0 := by
    have h6 : ((n : ℕ) : O ⧸ Ideal.span {((N : ℕ) : O)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    refine (congrFun (congrArg Subtype.val h4) N).trans ?_
    rw [MulMemClass.coe_mul, Pi.mul_apply, SubringClass.coe_natCast, Pi.natCast_apply, h6,
      zero_mul]
  rcases Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h5) with ⟨a, ha⟩
  have hxa : x = a := (isUnit_natCast_of_ne_zero hn).mul_left_cancel <|
    (congrArg Subtype.val ha).symm.trans <| by
      rw [MulMemClass.coe_mul, SubringClass.coe_natCast, Nat.cast_comm n (a : B)]
      rfl
  exact hxa ▸ a.2

/-- **Conjugation by `γ ∈ N_{B^×}(O)` in `B̂` preserves `Ô`, where it is the componentwise
conjugation**: `σ_γ(c) γ = γ c` in `B̂` for `c ∈ Ô`. -/
lemma oreDiv_mul_toFiniteAdelicAlgebra :
    (O.completedOrderConj γ c /ₒ 1) * O.toFiniteAdelicAlgebra hO (γ : Bˣ) =
      O.toFiniteAdelicAlgebra hO (γ : Bˣ) * (c /ₒ 1) := by
  rcases O.exists_natCast_mul_mem hO ((γ : Bˣ) : B) with ⟨n, hn, hnγ⟩
  rw [toFiniteAdelicAlgebra_apply, O.toFiniteAdelicAlgebraFun_eq hn hO hnγ, mul_div_one,
    oreDiv_mul_char _ _ _ _ (O.completedOrderConj γ c) (O.natDenom hn)
      (O.commute_completedOrderPosNat _ _).eq, mul_one, completedOrderConj_mul_toCompletedOrder]

end Subalgebra
