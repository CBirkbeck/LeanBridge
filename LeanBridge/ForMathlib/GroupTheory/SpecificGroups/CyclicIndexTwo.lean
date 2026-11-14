import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.MetacyclicPresentation
import Mathlib.GroupTheory.Complement
import TauCeti.GroupTheory.Index.Two
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Split and non-split extensions of a cyclic group by `C₂` acting by inversion

The dihedral group `Dₙ` is the split extension `Cₙ ⋊ C₂` in which `C₂` acts on `Cₙ` by `x ↦ x⁻¹`
(LMFDB `group.dihedral`). The dicyclic group `Dicₘ`, Mathlib's `QuaternionGroup m`, is a non-split
extension of `C₂ₘ` by `C₂`: its cyclic subgroup of index `2` has no complement, because every
element outside it squares to the central element of order `2` (LMFDB `group.dicyclic`,
`group.generalized_quaternion`). It is the only one: if a finite group `E` has a cyclic normal
subgroup `N` of index `2` with no complement, on which the elements outside `N` act by inversion,
then `|N|` is even and `E ≅ Dic_{|N|/2}` (LMFDB `group.dihedral`). Indeed for `b ∉ N` the square
`b²` lies in `N`, is inverted and fixed by `b`, so it has order at most `2`, and it is not `1` since
`⟨b⟩` would otherwise be a complement; so `b²` is the element of order `2` of `N`, and a generator
`a` of `N` and `b` satisfy the relations `a²ᵐ = 1`, `aᵐ = b²`, `b a b⁻¹ = a⁻¹` of `Dicₘ`.

## Main definitions

* `DihedralGroup.mulEquivSemidirectProduct` (LMFDB `group.dihedral`): `Dₙ ≃* Cₙ ⋊ C₂` with `C₂`
  acting by inversion.

## Main results

* `QuaternionGroup.not_isComplement'_quaternionRotations` (LMFDB `group.dicyclic`,
  `group.generalized_quaternion`, `group.dihedral`): the cyclic subgroup of index `2` of `Dicₘ`
  has no complement.
* `even_nat_card_of_forall_not_isComplement'` and
  `nonempty_mulEquiv_quaternionGroup_of_forall_not_isComplement'` (LMFDB `group.dihedral`): a
  non-split extension of a cyclic group `Cₙ` by `C₂` acting by inversion has `n` even and is the
  dicyclic group `Dic_{n/2}`.
* `SemidirectProduct.not_isMulCommutative_of_ne_one`: a semidirect product with a non-trivial
  action is not abelian.
* `SemiDihedralGroup.isCyclic_range_inl`, `SemiDihedralGroup.index_range_inl`,
  `SemiDihedralGroup.inl_mul_inr_ne_inr_mul_inl` (LMFDB `group.semi_dihedral`): the semi-dihedral
  group `SD_{2^k}` has a cyclic subgroup of index `2` and is non-abelian for `k ≥ 4`.
* `SemiDihedralGroup.mul_comm_three` (LMFDB `group.semi_dihedral`): `SD_8` is abelian.
-/

open Multiplicative SemidirectProduct Subgroup TauCeti ZMod

namespace QuaternionGroup

variable {m : ℕ}

lemma nat_card_quaternionRotations : Nat.card (quaternionRotations m) = 2 * m := by
  rw [Nat.card_congr (quaternionRotationsMulEquiv m).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

variable [NeZero m]

lemma mem_quaternionRotations_of_sq_eq_one {g : QuaternionGroup m} (hg : g ^ 2 = 1) :
    g ∈ quaternionRotations m := by
  rcases g with i | i
  · exact a_mem_quaternionRotations i
  · rw [xa_sq, ← a_zero, a.injEq, CharP.cast_eq_zero_iff (ZMod (2 * m)) (2 * m)] at hg
    have hm : m ≠ 0 := NeZero.ne m
    have hle : 2 * m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hg
    omega

/-- **The cyclic subgroup of index `2` of the dicyclic group `Dicₘ` has no complement** (LMFDB
`group.dicyclic`, `group.generalized_quaternion`, `group.dihedral`), so `Dicₘ` is a non-split
extension of `C₂ₘ` by `C₂`: an element of order `2` of a complement would lie outside the rotation
subgroup, but every element `xa i` outside it squares to `a m ≠ 1`. -/
lemma not_isComplement'_quaternionRotations (K : Subgroup (QuaternionGroup m)) :
    ¬(quaternionRotations m).IsComplement' K := fun hK ↦ by
  have hKcard : Nat.card K = 2 := by
    have h : Nat.card (quaternionRotations m) * Nat.card K = Nat.card (QuaternionGroup m) :=
      hK.card_mul_card
    rw [nat_card_quaternionRotations, Nat.card_eq_fintype_card (α := QuaternionGroup m),
      QuaternionGroup.card] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero two_ne_zero (NeZero.ne m)))
      (h.trans (by ring1))
  have : Nontrivial K := by
    rw [← Finite.one_lt_card_iff_nontrivial, hKcard]
    exact one_lt_two
  rcases exists_ne (1 : K) with ⟨k, hk⟩
  have hk2 : (k : QuaternionGroup m) ^ 2 = 1 := by
    rw [← hKcard, ← SubgroupClass.coe_pow, pow_card_eq_one', OneMemClass.coe_one]
  exact hk <| Subtype.ext <|
    disjoint_def.mp hK.disjoint (mem_quaternionRotations_of_sq_eq_one hk2) k.2

end QuaternionGroup

namespace DihedralGroup

variable (n : ℕ)

lemma neg_one_units_sq : (-1 : (ZMod n)ˣ) ^ 2 = 1 :=
  neg_one_sq

lemma involutionMulAut_neg_one_apply (x : Multiplicative (ZMod n)) :
    involutionMulAut (-1) (neg_one_units_sq n) (ofAdd 1) x = x⁻¹ := by
  rw [involutionMulAut_ofAdd_one, unitMulAut_apply, Units.val_neg, Units.val_one, neg_one_mul]
  rfl

variable [NeZero n]

lemma natCast_sub_one_eq_neg_one : ((n - 1 : ℕ) : ZMod n) = ((-1 : (ZMod n)ˣ) : ZMod n) := by
  rw [Nat.cast_sub NeZero.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub, Units.val_neg,
    Units.val_one]

lemma lift_relators_semidirectProduct : ∀ w ∈ relators n, FreeGroup.lift ![(inl (ofAdd 1) :
    Multiplicative (ZMod n) ⋊[involutionMulAut (-1) (neg_one_units_sq n)] Multiplicative (ZMod 2)),
    inr (ofAdd 1)] w = 1 := by
  rintro w (rfl | rfl | rfl)
  · simp [inl_ofAdd_one_pow]
  · simpa using inr_ofAdd_one_sq (neg_one_units_sq n)
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_inv_rev, inv_inv, ← mul_assoc,
      inr_mul_inl_mul_inv (neg_one_units_sq n) (natCast_sub_one_eq_neg_one n), zpow_natCast,
      ← pow_succ, Nat.sub_add_cancel NeZero.one_le, inl_ofAdd_one_pow]

/-- **The dihedral group `Dₙ` is the split extension `Cₙ ⋊ C₂` with `C₂` acting by `-1`** (LMFDB
`group.dihedral`), for `n ≠ 0`: the isomorphism sends the rotation `r 1` to the generator of `Cₙ`
and the reflection `sr 0` to that of `C₂`, which acts by `x ↦ x⁻¹`
(`DihedralGroup.involutionMulAut_neg_one_apply`). -/
noncomputable def mulEquivSemidirectProduct : DihedralGroup n ≃*
    Multiplicative (ZMod n) ⋊[involutionMulAut (-1) (neg_one_units_sq n)] Multiplicative (ZMod 2) :=
  (presentedGroupMulEquiv n).symm.trans <|
    MulEquiv.ofBijective (PresentedGroup.toGroup (lift_relators_semidirectProduct n)) <|
      bijective_of_closure_map_eq_top (NeZero.ne n) (presented_of_zero_pow n) (presented_conj n)
        (presented_of_one_sq n) (PresentedGroup.closure_of_zero_of_one _) _
        (by simpa using closure_inl_inr (neg_one_units_sq n)) <| by
          rw [SemidirectProduct.card, Nat.card_congr toAdd, Nat.card_congr toAdd, Nat.card_zmod,
            Nat.card_zmod, mul_comm]

end DihedralGroup

namespace SemidirectProduct

variable {N H : Type*} [Group N] [Group H] {φ : H →* MulAut N}

lemma index_range_inl_eq : (inl : N →* N ⋊[φ] H).range.index = Nat.card H := by
  rw [range_inl_eq_ker_rightHom, index_ker, MonoidHom.range_eq_top.mpr rightHom_surjective,
    card_top]

lemma isCyclic_range_inl [IsCyclic N] : IsCyclic (inl : N →* N ⋊[φ] H).range :=
  isCyclic_of_surjective _ (inl : N →* N ⋊[φ] H).rangeRestrict_surjective

/-- **A semidirect product with a non-trivial action is not abelian**: if `φ h n ≠ n`, then
`inr h * inl n = inl (φ h n) * inr h` differs from `inl n * inr h`. -/
lemma not_isMulCommutative_of_ne_one (hφ : φ ≠ 1) : ¬IsMulCommutative (N ⋊[φ] H) := fun hc ↦
  hφ <| MonoidHom.ext fun h ↦ MulEquiv.ext fun n ↦ by
    simpa using congrArg left (hc.is_comm.comm (inr h) (inl n))

end SemidirectProduct

variable {E : Type*} [Group E] {N : Subgroup E} {a b x : E}

lemma eq_one_or_eq_of_mem_zpowers (hb2 : b ^ 2 = 1) (hx : x ∈ zpowers b) : x = 1 ∨ x = b := by
  rcases mem_zpowers_iff.mp hx with ⟨k, rfl⟩
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_ofNat, hb2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_ofNat, hb2, one_zpow, one_mul]

lemma isComplement'_zpowers_of_sq_eq_one [Finite E] (hN : N.index = 2) (hb : b ∉ N)
    (hb2 : b ^ 2 = 1) : N.IsComplement' (zpowers b) := by
  refine isComplement'_of_card_mul_and_disjoint ?_ (disjoint_def.mpr fun hxN hxb ↦ ?_)
  · rw [Nat.card_zpowers, orderOf_eq_prime hb2 fun h ↦ hb (h ▸ one_mem N), ← hN, card_mul_index]
  · rcases eq_one_or_eq_of_mem_zpowers hb2 hxb with rfl | rfl
    · rfl
    · exact absurd hxN hb

lemma exists_notMem_of_index_eq_two (hN : N.index = 2) : ∃ b, b ∉ N := by
  by_contra h
  push Not at h
  have htop : N = ⊤ := eq_top_iff.mpr fun g _ ↦ h g
  rw [htop, index_top] at hN
  exact absurd hN (by decide)

lemma closure_pair_eq_top_of_index_eq_two (hN : (zpowers a).index = 2) (hb : b ∉ zpowers a) :
    closure {a, b} = ⊤ := by
  have hle : zpowers a ≤ closure {a, b} := zpowers_le.mpr (subset_closure (Set.mem_insert _ _))
  refine eq_top_iff.mpr fun y _ ↦ ?_
  by_cases hy : y ∈ zpowers a
  · exact hle hy
  · rw [← inv_mul_cancel_right y b]
    exact mul_mem (hle ((mul_mem_iff_of_index_two hN).mpr
      (iff_of_false hy fun h ↦ hb (inv_mem_iff.mp h))))
      (subset_closure (Set.mem_insert_of_mem _ rfl))

variable [Finite E]

lemma sq_ne_one_of_forall_not_isComplement' (hN : N.index = 2)
    (hns : ∀ K : Subgroup E, ¬N.IsComplement' K) (hb : b ∉ N) : b ^ 2 ≠ 1 :=
  fun hb2 ↦ hns _ (isComplement'_zpowers_of_sq_eq_one hN hb hb2)

/-- **A non-split extension of a cyclic group `Cₙ` by `C₂` acting by inversion has `n` even**
(LMFDB `group.dihedral`): for `b ∉ N`, the square `b²` is an element of order `2` of `N`. -/
lemma even_nat_card_of_forall_not_isComplement' (hN : N.index = 2)
    (hinv : ∀ g ∉ N, ∀ y ∈ N, g * y * g⁻¹ = y⁻¹) (hns : ∀ K : Subgroup E, ¬N.IsComplement' K) :
    Even (Nat.card N) := by
  rcases exists_notMem_of_index_eq_two hN with ⟨b, hb⟩
  have hord : orderOf (⟨b ^ 2, sq_mem_of_index_two hN b⟩ : N) = 2 := by
    rw [orderOf_mk]
    exact orderOf_eq_prime (sq_sq_eq_one_of_conj_eq_inv (sq_mem_of_index_two hN b) (hinv b hb))
      (sq_ne_one_of_forall_not_isComplement' hN hns hb)
  exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)

/-- **The non-split extension of `C₂ₘ` by `C₂` acting by inversion is the dicyclic group `Dicₘ`**
(LMFDB `group.dihedral`, `group.dicyclic`): a finite group with a cyclic subgroup `N` of order
`2m` and index `2` with no complement, on which the elements outside `N` act by inversion, is
isomorphic to `QuaternionGroup m`. A generator `a` of `N` and any `b ∉ N` satisfy the relations
`a²ᵐ = 1`, `aᵐ = b²`, `b a b⁻¹ = a⁻¹` of `Dicₘ`, since `b²` is the element of order `2` of `N`. -/
lemma nonempty_mulEquiv_quaternionGroup_of_forall_not_isComplement' [IsCyclic N] (hN : N.index = 2)
    (hinv : ∀ g ∉ N, ∀ y ∈ N, g * y * g⁻¹ = y⁻¹) (hns : ∀ K : Subgroup E, ¬N.IsComplement' K)
    {m : ℕ} (hm : Nat.card N = 2 * m) : Nonempty (E ≃* QuaternionGroup m) := by
  have : NeZero m := ⟨fun h ↦ Nat.card_pos.ne' (hm.trans (by rw [h, mul_zero]))⟩
  rcases N.isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic N› with ⟨a, rfl⟩
  have ha : orderOf a = 2 * m := (Nat.card_zpowers a).symm.trans hm
  rcases exists_notMem_of_index_eq_two hN with ⟨b, hb⟩
  have hx : a ^ (2 * m) = 1 := ha ▸ pow_orderOf_eq_one _
  have hb2 : b ^ 2 = a ^ (m : ℤ) := by
    rcases mem_zpowers_iff.mp (sq_mem_of_index_two hN b) with ⟨t, ht⟩
    have h1 : ((2 * m : ℕ) : ℤ) ∣ 2 * t := by
      rw [← ha]
      exact orderOf_dvd_iff_zpow_eq_one.mpr <| by
        rw [mul_comm, zpow_mul, ht, zpow_ofNat,
          sq_sq_eq_one_of_conj_eq_inv (sq_mem_of_index_two hN b) (hinv b hb)]
    have h2 : ¬((2 * m : ℕ) : ℤ) ∣ t := fun h ↦ sq_ne_one_of_forall_not_isComplement' hN hns hb <|
      ht.symm.trans <| orderOf_dvd_iff_zpow_eq_one.mp <| by rwa [ha]
    rcases h1 with ⟨q, hq⟩
    push_cast at hq h2
    have htq : t = m * q := by
      linarith
    rcases Int.even_or_odd q with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact absurd ⟨s, by rw [htq]; ring1⟩ h2
    · rw [← ht, htq, show (m : ℤ) * (2 * s + 1) = ((2 * m : ℕ) : ℤ) * s + m by push_cast; ring1,
        zpow_add, zpow_mul, zpow_natCast, hx, one_zpow, one_mul]
  have hyx : b * a * b⁻¹ = a ^ (-1 : ℤ) := (hinv b hb a (mem_zpowers a)).trans (zpow_neg_one _).symm
  have hlift : ∀ w ∈ QuaternionGroup.relators m, FreeGroup.lift ![a, b] w = 1 := by
    rintro w (rfl | rfl | rfl)
    · simp [hx]
    · simp [hb2]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [hyx, zpow_neg_one, inv_mul_cancel]
  have hcard : 2 * (2 * m) ≤ Nat.card E := by
    rw [← card_mul_index (zpowers a), hm, hN, mul_comm]
  exact ⟨(MulEquiv.ofBijective (PresentedGroup.toGroup hlift) <| bijective_of_closure_map_eq_top
    (mul_ne_zero two_ne_zero (NeZero.ne m)) (QuaternionGroup.presented_of_zero_pow m)
    (QuaternionGroup.presented_conj m) (QuaternionGroup.presented_of_one_sq m)
    (PresentedGroup.closure_of_zero_of_one _) _
    (by simpa using closure_pair_eq_top_of_index_eq_two hN hb) hcard).symm.trans
      (QuaternionGroup.presentedGroupMulEquiv m)⟩

namespace SemiDihedralGroup

variable (k : ℕ) [Fact (3 ≤ k)]

/-- **`SD_{2^k}` has a cyclic subgroup**, the image of `C_{2^{k-1}}`, of index `2`
(`SemiDihedralGroup.index_range_inl`) (LMFDB `group.semi_dihedral`). -/
lemma isCyclic_range_inl : IsCyclic (inl : _ →* SemiDihedralGroup k).range :=
  SemidirectProduct.isCyclic_range_inl

/-- **The image of `C_{2^{k-1}}` in `SD_{2^k}` has index `2`** (LMFDB `group.semi_dihedral`). -/
lemma index_range_inl : (inl : _ →* SemiDihedralGroup k).range.index = 2 :=
  index_range_inl_eq.trans <| (Nat.card_congr toAdd).trans (Nat.card_zmod 2)

lemma val_semiDihedralUnit_ne_one (hk : 4 ≤ k) : (semiDihedralUnit k : ZMod (2 ^ (k - 1))) ≠ 1 := by
  rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
  intro h
  have h' : (2 : ZMod (2 ^ (4 + j - 1))) ^ (4 + j - 2) - 1 = 1 := h
  rw [show 4 + j - 1 = j + 3 by omega, show 4 + j - 2 = j + 2 by omega] at h'
  have h2 : ((2 ^ (j + 2) : ℕ) : ZMod (2 ^ (j + 3))) = ((2 : ℕ) : ZMod (2 ^ (j + 3))) := by
    push_cast
    linear_combination h'
  have h4 : 2 ^ 2 ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (j + 2) < 2 ^ (j + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- **`SD_{2^k}` is non-abelian for `k ≥ 4`** (LMFDB `group.semi_dihedral`): the generator of `C₂`
does not commute with that of `C_{2^{k-1}}`, which it sends to its power `2^{k-2} - 1 ≠ 1`. -/
lemma inl_mul_inr_ne_inr_mul_inl (hk : 4 ≤ k) :
    (inl (ofAdd 1) * inr (ofAdd 1) : SemiDihedralGroup k) ≠ inr (ofAdd 1) * inl (ofAdd 1) :=
  fun h ↦ val_semiDihedralUnit_ne_one k hk <| by
    simpa [involutionMulAut_ofAdd_one, unitMulAut_apply] using (congrArg (toAdd ∘ left) h).symm

variable [Fact (3 ≤ 3)] in
/-- **`SD_8` is abelian** (LMFDB `group.semi_dihedral`): for `k = 3` the generator of `C₂` acts on
`C₄` by `x ↦ x ^ (2 - 1) = x`, so the knowl's `SD_{2^k}` is non-abelian only for `k ≥ 4`. -/
lemma mul_comm_three (g₁ g₂ : SemiDihedralGroup 3) : g₁ * g₂ = g₂ * g₁ := by
  have hu : semiDihedralUnit 3 = 1 := Units.ext rfl
  have hφ (h : Multiplicative (ZMod 2)) :
      involutionMulAut _ (semiDihedralUnit_pow_two 3) h = 1 := by
    ext z
    simp [involutionMulAut, unitPowMulAut_apply, hu]
  ext <;> simp [hφ, mul_comm]

end SemiDihedralGroup
