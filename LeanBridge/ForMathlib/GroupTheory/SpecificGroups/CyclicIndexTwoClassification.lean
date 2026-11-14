import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.CyclicIndexTwo
import Mathlib.GroupTheory.IndexNormal

/-!
# Non-abelian `2`-groups with a cyclic subgroup of index `2`

For `k ≥ 4` there are exactly four non-abelian groups of order `2 ^ k` with a cyclic subgroup of
index `2`, up to isomorphism (LMFDB `group.semi_dihedral`, `group.other_dihedral`): the dihedral
group `D_{2^{k-1}}` of order `2 ^ k`, the generalised quaternion group `Q_{2^k}`, Mathlib's
`QuaternionGroup (2 ^ (k - 2))`, the semi-dihedral group `SD_{2^k}` and the other-dihedral group
`OD_{2^k}`.

Let `⟨a⟩` be a cyclic subgroup of order `n = 2 ^ (k - 1)` and index `2` of `G`, and `b ∉ ⟨a⟩`.
Then `b a b⁻¹ = a ^ e` with `e² ≡ 1` modulo `n`, since `b²` lies in `⟨a⟩` and commutes with `a`;
so `e ≡ ±1` modulo `n / 2`, and `e` is `-1`, `n / 2 - 1` or `n / 2 + 1` modulo `n`, the value `1`
being excluded as `G` is not abelian. Write `b² = a ^ s`: then `(e - 1) s ≡ 0` and
`(b aⁱ)² = a ^ ((e + 1) i + s)`. For `e = n / 2 ± 1` this vanishes for a suitable `i`, so `G` has
an involution `c ∉ ⟨a⟩`, and the presentation `⟨r, s | rⁿ = s² = 1, s r s = r ^ e⟩` identifies
`G` with `C_n ⋊ C_2`, that is with `OD_{2^k}` or `SD_{2^k}`. For `e = -1` the same holds when some
element outside `⟨a⟩` is an involution, giving `D_{2^{k-1}}`; otherwise `⟨a⟩` has no complement,
and `G` is the dicyclic group `Q_{2^k}`.

The four groups are pairwise non-isomorphic, since they have `2 ^ (k - 1) + 2`, `2`,
`2 ^ (k - 2) + 2` and `4` solutions of `g² = 1` respectively. In `C_n ⋊ C_2` with `C_2` acting by
`x ↦ x ^ u` these solutions are the `x` with `2 x = 0` and the `x s` with `(1 + u) x = 0`.

## Main results

* `nonempty_mulEquiv_semidirectProduct_of_sq_eq_one`: a group with a cyclic subgroup `⟨a⟩ ≅ C_n`
  of index `2` and an involution `c ∉ ⟨a⟩` with `c a c⁻¹ = a ^ e` is `C_n ⋊ C_2`, with `C_2` acting
  by `x ↦ x ^ e`.
* `nonempty_mulEquiv_of_isCyclic_of_index_eq_two` (LMFDB `group.semi_dihedral`,
  `group.other_dihedral`): a non-abelian group of order `2 ^ k`, `k ≥ 4`, with a cyclic subgroup of
  index `2` is isomorphic to `D_{2^{k-1}}`, `Q_{2^k}`, `SD_{2^k}` or `OD_{2^k}`.
* `QuaternionGroup.not_isMulCommutative`, `SemiDihedralGroup.not_isMulCommutative`,
  `OtherDihedralGroup.not_isMulCommutative`, `OtherDihedralGroup.isCyclic_range_inl`,
  `OtherDihedralGroup.index_range_inl`: these groups are non-abelian, and `OD_{2^k}` has a cyclic
  subgroup of index `2`.
* `DihedralGroup.isEmpty_mulEquiv_quaternionGroup`,
  `DihedralGroup.isEmpty_mulEquiv_semiDihedralGroup`,
  `DihedralGroup.isEmpty_mulEquiv_otherDihedralGroup`,
  `QuaternionGroup.isEmpty_mulEquiv_semiDihedralGroup`,
  `QuaternionGroup.isEmpty_mulEquiv_otherDihedralGroup`,
  `SemiDihedralGroup.isEmpty_mulEquiv_otherDihedralGroup`: the four groups are pairwise
  non-isomorphic for `k ≥ 4`.
-/

open Multiplicative SemidirectProduct Subgroup ZMod

lemma Int.two_pow_dvd_sub_one_or_two_pow_dvd_add_one {m : ℕ} {e : ℤ} (h : 2 ^ (m + 1) ∣ e ^ 2 - 1) :
    2 ^ m ∣ e - 1 ∨ 2 ^ m ∣ e + 1 := by
  have hodd : Odd e := by
    have h2 : (2 : ℤ) ∣ e ^ 2 - 1 := (dvd_pow_self 2 m.succ_ne_zero).trans h
    rw [← even_iff_two_dvd, Int.even_sub_one, Int.even_pow' two_ne_zero] at h2
    exact Int.not_even_iff_odd.mp h2
  rcases m with _ | m
  · simp
  rcases hodd with ⟨x, rfl⟩
  have hm : (2 : ℤ) ^ m ∣ x * (x + 1) := by
    refine (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp ?_
    rw [show 4 * (x * (x + 1)) = (2 * x + 1) ^ 2 - 1 by ring1,
      show (4 : ℤ) * 2 ^ m = 2 ^ (m + 2) by ring1]
    exact h
  rcases Int.even_or_odd x with hx | hx
  · left
    rw [add_sub_cancel_right, pow_succ']
    exact mul_dvd_mul_left 2 <| hx.add_one.isCoprime_two.symm.pow_left.dvd_of_dvd_mul_right hm
  · right
    rw [show 2 * x + 1 + 1 = 2 * (x + 1) by ring1, pow_succ']
    exact mul_dvd_mul_left 2 <| hx.isCoprime_two.symm.pow_left.dvd_of_dvd_mul_left hm

variable {G : Type*} [Group G] {N : Subgroup G} {a b c : G} {k m n : ℕ} [Fact (3 ≤ k)]

/-- **A group with a cyclic subgroup `⟨a⟩ ≅ C_n` of index `2` and an involution `c ∉ ⟨a⟩` acting
by `a ↦ a ^ E` is the semidirect product `C_n ⋊ C_2`** in which `C_2` acts by `x ↦ x ^ E`: the
presented group `⟨r, s | rⁿ = s² = 1, s r s = r ^ E⟩` maps onto it and has at most `2n`
elements. -/
lemma nonempty_mulEquiv_semidirectProduct_of_sq_eq_one (hN : (zpowers a).index = 2) [NeZero n]
    (ha : orderOf a = n) (hc : c ∉ zpowers a) (hc2 : c ^ 2 = 1) {E : ℕ} {u : (ZMod n)ˣ}
    (hu : u ^ 2 = 1) (hE : (E : ZMod n) = u) (hca : c * a * c⁻¹ = a ^ E) :
    Nonempty (G ≃* Multiplicative (ZMod n) ⋊[involutionMulAut u hu] Multiplicative (ZMod 2)) := by
  have hlift : ∀ w ∈ involutionRelators n E, FreeGroup.lift ![a, c] w = 1 := by
    rintro w (rfl | rfl | rfl)
    · simp [← ha]
    · simp [hc2]
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [mul_inv_eq_one, ← hca, inv_eq_of_mul_eq_one_right ((pow_two c).symm.trans hc2)]
  have hcard : 2 * n ≤ Nat.card G := by
    rw [← card_mul_index (zpowers a), hN, Nat.card_zpowers, ha, mul_comm]
  exact ⟨(MulEquiv.ofBijective (PresentedGroup.toGroup hlift) <| bijective_of_closure_map_eq_top
    (NeZero.ne n) PresentedGroup.involution_of_zero_pow PresentedGroup.involution_conj
    (PresentedGroup.involution_of_one_sq.trans (zpow_zero _).symm)
    (PresentedGroup.closure_of_zero_of_one _) _
    (by simpa using closure_pair_eq_top_of_index_eq_two hN hc) hcard).symm.trans
      (involutionPresentedGroupMulEquiv hu hE)⟩

private lemma nonempty_mulEquiv_semidirectProduct_of_dvd (hN : (zpowers a).index = 2) [NeZero n]
    (ha : orderOf a = n) (hb : b ∉ zpowers a) {e s i : ℤ} (he : b * a * b⁻¹ = a ^ e)
    (hs : b ^ 2 = a ^ s) (hi : (n : ℤ) ∣ (e + 1) * i + s) {E : ℕ} {u : (ZMod n)ˣ} (hu : u ^ 2 = 1)
    (hE : (E : ZMod n) = u) (heE : (n : ℤ) ∣ e - E) :
    Nonempty (G ≃* Multiplicative (ZMod n) ⋊[involutionMulAut u hu] Multiplicative (ZMod 2)) := by
  have hmem : a ^ i ∈ zpowers a := zpow_mem (mem_zpowers a) i
  refine nonempty_mulEquiv_semidirectProduct_of_sq_eq_one hN ha (c := b * a ^ i)
    (fun h ↦ hb ?_) ?_ hu hE ?_
  · simpa using mul_mem h (inv_mem hmem)
  · have h1 : (b * a ^ i) ^ 2 = b * a ^ i * b⁻¹ * b ^ 2 * a ^ i := by
      rw [pow_two, pow_two]
      group
    rw [h1, ← conj_zpow, he, hs, ← zpow_mul, ← zpow_add, ← zpow_add,
      ← orderOf_dvd_iff_zpow_eq_one, ha, show e * i + s + i = (e + 1) * i + s by ring1]
    exact hi
  · have h2 : b * a ^ i * a * (b * a ^ i)⁻¹ = b * a * b⁻¹ := by
      group
    rw [h2, he, ← zpow_natCast, ← mul_inv_eq_one, ← zpow_sub, ← orderOf_dvd_iff_zpow_eq_one, ha]
    exact heE

private lemma exists_notMem_sq_eq_one_of_isComplement' [Finite G] (hN : N.index = 2)
    {K : Subgroup G} (hK : N.IsComplement' K) : ∃ c ∉ N, c ^ 2 = 1 := by
  have hKcard : Nat.card K = 2 := hK.symm.index_eq_card.symm.trans hN
  have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by rw [hKcard]; norm_num)
  rcases exists_ne (1 : K) with ⟨c, hc⟩
  refine ⟨c, fun h ↦ hc (Subtype.ext (disjoint_def.mp hK.disjoint h c.2)), ?_⟩
  rw [← hKcard, ← SubgroupClass.coe_pow, pow_card_eq_one', OneMemClass.coe_one]

/-- **The non-abelian groups of order `2 ^ k`, `k ≥ 4`, with a cyclic subgroup of index `2`**
(LMFDB `group.semi_dihedral`, `group.other_dihedral`): such a group is isomorphic to the dihedral
group `D_{2^{k-1}}` of order `2 ^ k`, the generalised quaternion group `Q_{2^k}`, the semi-dihedral
group `SD_{2^k}` or the other-dihedral group `OD_{2^k}`. For a generator `a` of the cyclic
subgroup and `b` outside it, `b a b⁻¹ = a ^ e` with `e ≡ -1` or `2 ^ (k - 2) ± 1` modulo
`2 ^ (k - 1)`; for `e = 2 ^ (k - 2) ± 1` the coset of `b` contains an involution, and for `e = -1`
the group is dihedral or dicyclic according as it contains one. -/
lemma nonempty_mulEquiv_of_isCyclic_of_index_eq_two (hk : 4 ≤ k) (hG : Nat.card G = 2 ^ k)
    [IsCyclic N] (hN : N.index = 2) (hnc : ¬IsMulCommutative G) :
    Nonempty (G ≃* DihedralGroup (2 ^ (k - 1))) ∨ Nonempty (G ≃* QuaternionGroup (2 ^ (k - 2))) ∨
      Nonempty (G ≃* SemiDihedralGroup k) ∨ Nonempty (G ≃* OtherDihedralGroup k) := by
  have : Finite G := Nat.finite_of_card_ne_zero (hG ▸ (pow_pos two_pos k).ne')
  have : NeZero (2 ^ (k - 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  set R : ℤ := 2 ^ (k - 4) with hR
  have h1 : (2 : ℤ) ^ (k - 1) = 8 * R := by
    rw [hR, show k - 1 = k - 4 + 3 by omega, pow_add]
    ring1
  have h2 : (2 : ℤ) ^ (k - 2) = 4 * R := by
    rw [hR, show k - 2 = k - 4 + 2 by omega, pow_add]
    ring1
  have h3 : (2 : ℤ) ^ (k - 3) = 2 * R := by
    rw [hR, show k - 3 = k - 4 + 1 by omega, pow_add]
    ring1
  rcases N.isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic N› with ⟨a, rfl⟩
  have hNcard : Nat.card (zpowers a) = 2 ^ (k - 1) := by
    have h : Nat.card (zpowers a) * (zpowers a).index = Nat.card G := card_mul_index _
    rw [hN, hG, show k = k - 1 + 1 by omega, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right two_pos h
  have ha : orderOf a = 2 ^ (k - 1) := (Nat.card_zpowers a).symm.trans hNcard
  have hdvd (z : ℤ) : a ^ z = 1 ↔ (2 : ℤ) ^ (k - 1) ∣ z := by
    rw [← orderOf_dvd_iff_zpow_eq_one, ha]
    push_cast
    rfl
  rcases exists_notMem_of_index_eq_two hN with ⟨b, hb⟩
  rcases mem_zpowers_iff.mp ((normal_of_index_eq_two hN).conj_mem a (mem_zpowers a) b) with
    ⟨e, he⟩
  rcases mem_zpowers_iff.mp (sq_mem_of_index_two hN b) with ⟨s, hs⟩
  have hconj (z : ℤ) : b * a ^ z * b⁻¹ = a ^ (e * z) := by
    rw [← conj_zpow, ← he, ← zpow_mul]
  have hee : (2 : ℤ) ^ (k - 1) ∣ e ^ 2 - 1 := by
    have h : b ^ 2 * a * (b ^ 2)⁻¹ = a := by
      rw [← hs, (Commute.zpow_self a s).eq, mul_inv_cancel_right]
    have h' : b ^ 2 * a * (b ^ 2)⁻¹ = b * (b * a * b⁻¹) * b⁻¹ := by
      rw [pow_two]
      group
    rw [h', ← he, hconj] at h
    rw [← hdvd, sq, zpow_sub, zpow_one, h, mul_inv_cancel]
  have hes : (2 : ℤ) ^ (k - 1) ∣ (e - 1) * s := by
    have h : b * b ^ 2 * b⁻¹ = b ^ 2 := by
      rw [pow_two]
      group
    rw [← hs, hconj] at h
    rw [← hdvd, sub_mul, one_mul, zpow_sub, h, mul_inv_cancel]
  have hne : ¬(2 : ℤ) ^ (k - 1) ∣ e - 1 := fun h ↦ hnc <| by
    have hab : b * a * b⁻¹ = a := by
      rw [← he, ← mul_inv_eq_one, ← zpow_sub_one, (hdvd _).mpr h]
    have hcomm : Commute a b := (mul_inv_eq_iff_eq_mul.mp hab).symm
    have htop : closure {a, b} = ⊤ := closure_pair_eq_top_of_index_eq_two hN hb
    have : IsMulCommutative (closure {a, b}) :=
      isMulCommutative_closure (Set.pairwise_pair.mpr fun _ ↦ ⟨hcomm, hcomm.symm⟩)
    refine isMulCommutative_iff.mpr fun x y ↦ ?_
    exact congrArg Subtype.val (mul_comm' (⟨x, htop ▸ mem_top x⟩ : closure {a, b})
      ⟨y, htop ▸ mem_top y⟩)
  have hconjc (c : G) (hc : c ∉ zpowers a) : c * a * c⁻¹ = a ^ e := by
    have hy : b⁻¹ * c ∈ zpowers a :=
      (mul_mem_iff_of_index_two hN).mpr (iff_of_false (fun h ↦ hb (inv_mem_iff.mp h)) hc)
    rcases mem_zpowers_iff.mp hy with ⟨z, hz⟩
    have hcz : c = b * a ^ z := by
      rw [hz, mul_inv_cancel_left]
    rw [hcz, he]
    group
  rcases Int.two_pow_dvd_sub_one_or_two_pow_dvd_add_one (m := k - 2)
    (by rwa [show k - 2 + 1 = k - 1 by omega]) with ⟨t, ht⟩ | ⟨t, ht⟩
  · have htodd : Odd t := by
      refine Int.not_even_iff_odd.mp fun ⟨t', htt⟩ ↦ hne ⟨t', ?_⟩
      rw [ht, htt, h1, h2]
      ring1
    have hs2 : (2 : ℤ) ∣ s := by
      have h : (2 : ℤ) ^ (k - 2) * 2 ∣ 2 ^ (k - 2) * (t * s) := by
        rw [← mul_assoc, ← ht, h2, show 4 * R * 2 = 2 ^ (k - 1) by rw [h1]; ring1]
        exact hes
      exact htodd.isCoprime_two.symm.dvd_of_dvd_mul_left
        ((mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)).mp h)
    rcases hs2 with ⟨s', rfl⟩
    have he' : e = 1 + 4 * R * t := by
      rw [← h2]
      linarith
    refine Or.inr (Or.inr (Or.inr (nonempty_mulEquiv_semidirectProduct_of_dvd hN ha hb he.symm
      hs.symm (i := -s' * (1 - 2 ^ (k - 3) * t)) ?_ (otherDihedralUnit_pow_two k)
      (natCast_two_pow_add_one_eq k) ?_)))
    · push_cast
      rw [h1, h3, he']
      exact ⟨R * t ^ 2 * s', by ring1⟩
    · rcases htodd with ⟨t', rfl⟩
      push_cast
      rw [h1, h2, he']
      exact ⟨t', by ring1⟩
  · rcases Int.even_or_odd t with ⟨t', rfl⟩ | htodd
    · have he1 : (2 : ℤ) ^ (k - 1) ∣ e + 1 := ⟨t', by rw [ht, h1, h2]; ring1⟩
      have hae : a ^ e = a⁻¹ := by
        rw [← mul_eq_one_iff_eq_inv, ← zpow_add_one, hdvd]
        exact he1
      have hinv (c : G) (hc : c ∉ zpowers a) (y : G) (hy : y ∈ zpowers a) : c * y * c⁻¹ = y⁻¹ := by
        rcases mem_zpowers_iff.mp hy with ⟨z, rfl⟩
        rw [← conj_zpow, hconjc c hc, hae, inv_zpow]
      by_cases hsplit : ∃ c ∉ zpowers a, c ^ 2 = 1
      · rcases hsplit with ⟨c, hc, hc2⟩
        refine Or.inl ⟨(nonempty_mulEquiv_semidirectProduct_of_sq_eq_one hN ha hc hc2
          (DihedralGroup.neg_one_units_sq _) (DihedralGroup.natCast_sub_one_eq_neg_one _)
          ?_).some.trans (DihedralGroup.mulEquivSemidirectProduct _).symm⟩
        rw [hconjc c hc, ← zpow_natCast, ← mul_inv_eq_one, ← zpow_sub, hdvd,
          Nat.cast_sub Nat.one_le_two_pow]
        push_cast
        rw [show e - (2 ^ (k - 1) - 1) = e + 1 - 2 ^ (k - 1) by ring1]
        exact he1.sub dvd_rfl
      · refine Or.inr (Or.inl (nonempty_mulEquiv_quaternionGroup_of_forall_not_isComplement' hN
          hinv (fun K hK ↦ hsplit (exists_notMem_sq_eq_one_of_isComplement' hN hK)) ?_))
        rw [hNcard, ← pow_succ', show k - 2 + 1 = k - 1 by omega]
    · have hodd : Odd ((2 : ℤ) ^ (k - 3) * t - 1) := ⟨R * t - 1, by rw [h3]; ring1⟩
      have he' : e = 4 * R * t - 1 := by
        rw [← h2]
        linarith
      have hs4 : (2 : ℤ) ^ (k - 2) ∣ s := by
        have h : (2 : ℤ) * 2 ^ (k - 2) ∣ 2 * ((2 ^ (k - 3) * t - 1) * s) := by
          rw [h2, h3, show 2 * (4 * R) = 2 ^ (k - 1) by rw [h1]; ring1,
            show 2 * ((2 * R * t - 1) * s) = (e - 1) * s by rw [he']; ring1]
          exact hes
        exact hodd.isCoprime_two.symm.pow_left.dvd_of_dvd_mul_left
          ((mul_dvd_mul_iff_left two_ne_zero).mp h)
      rcases hs4 with ⟨s', rfl⟩
      refine Or.inr (Or.inr (Or.inl (nonempty_mulEquiv_semidirectProduct_of_dvd hN ha hb he.symm
        hs.symm (i := s') ?_ (semiDihedralUnit_pow_two k) (natCast_two_pow_sub_one_eq k) ?_)))
      · rcases htodd with ⟨t', rfl⟩
        push_cast
        rw [h1, h2, he']
        exact ⟨s' * (t' + 1), by ring1⟩
      · rcases htodd with ⟨t', rfl⟩
        rw [Nat.cast_sub Nat.one_le_two_pow]
        push_cast
        rw [h1, h2, he']
        exact ⟨t', by ring1⟩

lemma DihedralGroup.nat_card_two_pow : Nat.card (DihedralGroup (2 ^ (k - 1))) = 2 ^ k := by
  have hk : 3 ≤ k := Fact.out
  rw [nat_card, ← pow_succ', Nat.sub_add_cancel (by omega)]

lemma QuaternionGroup.nat_card_two_pow : Nat.card (QuaternionGroup (2 ^ (k - 2))) = 2 ^ k := by
  have hk : 3 ≤ k := Fact.out
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [Nat.card_eq_fintype_card, card, show 4 = 2 ^ 2 by norm_num, ← pow_add,
    Nat.add_sub_cancel' (by omega)]

/-- **The generalised quaternion group `QuaternionGroup m` is non-abelian for `m ≥ 2`** (LMFDB
`group.semi_dihedral`, `group.other_dihedral`): `a 1` and `xa 0` do not commute, as `-1 ≠ 1` in
`ZMod (2 m)`. -/
lemma QuaternionGroup.not_isMulCommutative (hm : 2 ≤ m) :
    ¬IsMulCommutative (QuaternionGroup m) := fun h ↦ by
  have h' : (a 1 : QuaternionGroup m) * xa 0 = xa 0 * a 1 := h.is_comm.comm _ _
  rw [a_mul_xa, xa_mul_a, xa.injEq, zero_sub, zero_add, neg_eq_iff_add_eq_zero,
    one_add_one_eq_two] at h'
  have h2 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by
    exact_mod_cast h'
  have h2m : 2 * m ≤ 2 := Nat.le_of_dvd two_pos ((natCast_eq_zero_iff _ _).mp h2)
  omega

/-- **The semi-dihedral group `SD_{2^k}` is non-abelian for `k ≥ 4`** (LMFDB
`group.semi_dihedral`). -/
lemma SemiDihedralGroup.not_isMulCommutative (hk : 4 ≤ k) :
    ¬IsMulCommutative (SemiDihedralGroup k) :=
  not_isMulCommutative_of_ne_one <| unitPowMulAut_ne_one _ _ (val_semiDihedralUnit_ne_one k hk)

namespace OtherDihedralGroup

variable (k)

/-- **`OD_{2^k}` has a cyclic subgroup**, the image of `C_{2^{k-1}}`, of index `2`
(`OtherDihedralGroup.index_range_inl`) (LMFDB `group.other_dihedral`). -/
lemma isCyclic_range_inl : IsCyclic (inl : _ →* OtherDihedralGroup k).range :=
  SemidirectProduct.isCyclic_range_inl

/-- **The image of `C_{2^{k-1}}` in `OD_{2^k}` has index `2`** (LMFDB `group.other_dihedral`). -/
lemma index_range_inl : (inl : _ →* OtherDihedralGroup k).range.index = 2 :=
  index_range_inl_eq.trans <| (Nat.card_congr toAdd).trans (Nat.card_zmod 2)

lemma val_otherDihedralUnit_ne_one : (otherDihedralUnit k : ZMod (2 ^ (k - 1))) ≠ 1 := fun h ↦ by
  have hk : 3 ≤ k := Fact.out
  have h' : ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ (k - 1))) = 0 := by
    have hu : (otherDihedralUnit k : ZMod (2 ^ (k - 1))) = 2 ^ (k - 2) + 1 := rfl
    push_cast
    linear_combination hu.symm.trans h
  rw [natCast_eq_zero_iff] at h'
  have hle : 2 ^ (k - 1) ≤ 2 ^ (k - 2) := Nat.le_of_dvd (Nat.two_pow_pos _) h'
  have hlt : 2 ^ (k - 2) < 2 ^ (k - 1) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : k - 2 < k - 1)
  omega

/-- **The other-dihedral group `OD_{2^k}` is non-abelian** (LMFDB `group.other_dihedral`): the
generator of `C_2` sends that of `C_{2^{k-1}}` to its power `2 ^ (k - 2) + 1 ≠ 1`. -/
lemma not_isMulCommutative : ¬IsMulCommutative (OtherDihedralGroup k) :=
  not_isMulCommutative_of_ne_one <| unitPowMulAut_ne_one _ _ (val_otherDihedralUnit_ne_one k)

end OtherDihedralGroup

lemma MulEquiv.card_sq_eq_one {H : Type*} [Group H] (f : G ≃* H) :
    Nat.card {g : G // g ^ 2 = 1} = Nat.card {h : H // h ^ 2 = 1} :=
  Nat.card_congr <| f.toEquiv.subtypeEquiv fun g ↦ by
    rw [← f.map_eq_one_iff, map_pow]
    rfl

lemma ZMod.card_mul_eq_zero_of_dvd {d : ℕ} [NeZero n] (hd : d ∣ n) :
    Nat.card {x : ZMod n // (d : ZMod n) * x = 0} = d := by
  classical
  have hd0 : d ≠ 0 := fun h ↦ NeZero.ne n (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [← nsmul_eq_mul]
  rw [← sum_card_addOrderOf_eq_card_nsmul_eq_zero hd0]
  refine (Finset.sum_congr rfl fun m hm ↦ IsAddCyclic.card_addOrderOf_eq_totient ?_).trans
    (Nat.sum_totient d)
  rw [ZMod.card]
  exact (Nat.dvd_of_mem_divisors hm).trans hd

lemma ZMod.card_two_mul_eq_zero [NeZero n] (hn : 2 ∣ n) :
    Nat.card {x : ZMod n // 2 * x = 0} = 2 := by
  simpa using card_mul_eq_zero_of_dvd hn

section SemidirectProduct

variable {u : (ZMod n)ˣ} (hu : u ^ 2 = 1)

private lemma sq_mk_one (y : ZMod n) :
    (⟨ofAdd y, 1⟩ : Multiplicative (ZMod n) ⋊[involutionMulAut u hu] Multiplicative (ZMod 2)) ^ 2 =
      ⟨ofAdd (2 * y), 1⟩ := by
  ext
  · simp [pow_two, two_mul]
  · simp [pow_two]

private lemma sq_mk_ofAdd_one (y : ZMod n) :
    (⟨ofAdd y, ofAdd 1⟩ : Multiplicative (ZMod n) ⋊[involutionMulAut u hu]
      Multiplicative (ZMod 2)) ^ 2 = ⟨ofAdd ((1 + u) * y), 1⟩ := by
  ext
  · simp [pow_two, involutionMulAut_ofAdd_one, unitMulAut_apply, add_mul]
  · simp [pow_two]
    rfl

variable [NeZero n] in
lemma card_sq_eq_one_semidirectProduct :
    Nat.card {g : Multiplicative (ZMod n) ⋊[involutionMulAut u hu] Multiplicative (ZMod 2) //
      g ^ 2 = 1} = Nat.card {x : ZMod n // 2 * x = 0} +
        Nat.card {x : ZMod n // (1 + u) * x = 0} := by
  let f₀ : ZMod n → Multiplicative (ZMod n) ⋊[involutionMulAut u hu] Multiplicative (ZMod 2) :=
    fun y ↦ ⟨ofAdd y, 1⟩
  let f₁ : ZMod n → Multiplicative (ZMod n) ⋊[involutionMulAut u hu] Multiplicative (ZMod 2) :=
    fun y ↦ ⟨ofAdd y, ofAdd 1⟩
  have hS : {g | g ^ 2 = 1} = f₀ '' {y | 2 * y = 0} ∪ f₁ '' {y | (1 + u) * y = 0} := by
    ext ⟨x, ε⟩
    rcases (⟨toAdd x, rfl⟩ : ∃ y, ofAdd y = x) with ⟨y, rfl⟩
    rcases (⟨toAdd ε, rfl⟩ : ∃ e, ofAdd e = ε) with ⟨e, rfl⟩
    have h1 : (1 : Multiplicative (ZMod 2)) ≠ ofAdd 1 := by
      decide
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) e with rfl | rfl
    · rw [ofAdd_zero, Set.mem_ofPred_eq, sq_mk_one]
      simp [f₀, f₁, SemidirectProduct.ext_iff]
    · rw [Set.mem_ofPred_eq, sq_mk_ofAdd_one]
      simp [f₀, f₁, SemidirectProduct.ext_iff, h1]
  have hinj₀ : Function.Injective f₀ := fun y y' h ↦ by
    simpa [f₀] using h
  have hinj₁ : Function.Injective f₁ := fun y y' h ↦ by
    simpa [f₁] using h
  have hdisj : Disjoint (f₀ '' {y | 2 * y = 0}) (f₁ '' {y | (1 + u) * y = 0}) := by
    refine Set.disjoint_left.mpr ?_
    rintro - ⟨y, -, rfl⟩ ⟨y', -, h⟩
    simp [f₀, f₁, SemidirectProduct.ext_iff] at h
  refine (congrArg Set.ncard hS).trans ?_
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ hinj₀, Set.ncard_image_of_injective _ hinj₁]
  rfl

end SemidirectProduct

lemma DihedralGroup.card_sq_eq_one [NeZero n] (hn : 2 ∣ n) :
    Nat.card {g : DihedralGroup n // g ^ 2 = 1} = n + 2 := by
  rw [(mulEquivSemidirectProduct n).card_sq_eq_one, card_sq_eq_one_semidirectProduct,
    ZMod.card_two_mul_eq_zero hn, add_comm]
  simp

lemma QuaternionGroup.card_sq_eq_one [NeZero m] :
    Nat.card {g : QuaternionGroup m // g ^ 2 = 1} = 2 := by
  have ha1 (j : ZMod (2 * m)) : (a j : QuaternionGroup m) = 1 ↔ j = 0 := by
    rw [← a_zero, a.injEq]
  have hS : {g : QuaternionGroup m | g ^ 2 = 1} = a '' {i | 2 * i = 0} := by
    ext (i | i)
    · simp [pow_two, ha1, two_mul]
    · have hm : (m : ZMod (2 * m)) ≠ 0 := by
        rw [Ne, natCast_eq_zero_iff]
        exact fun h ↦ NeZero.ne m (Nat.eq_zero_of_dvd_of_lt h (lt_two_mul_self (NeZero.pos m)))
      simp [ha1, hm]
  refine (congrArg Set.ncard hS).trans ?_
  rw [Set.ncard_image_of_injective _ fun i j hij ↦ a.inj hij]
  exact ZMod.card_two_mul_eq_zero (dvd_mul_right 2 m)

lemma SemiDihedralGroup.card_sq_eq_one :
    Nat.card {g : SemiDihedralGroup k // g ^ 2 = 1} = 2 ^ (k - 2) + 2 := by
  have hk : 3 ≤ k := Fact.out
  have : NeZero (2 ^ (k - 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hiff (x : ZMod (2 ^ (k - 1))) : (1 + (semiDihedralUnit k : ZMod (2 ^ (k - 1)))) * x = 0 ↔
      ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ (k - 1))) * x = 0 := by
    simp [semiDihedralUnit]
  rw [card_sq_eq_one_semidirectProduct, ZMod.card_two_mul_eq_zero (dvd_pow_self 2 (by omega)),
    Nat.card_congr (Equiv.subtypeEquivRight hiff),
    card_mul_eq_zero_of_dvd (pow_dvd_pow 2 (by omega)), add_comm]

lemma OtherDihedralGroup.card_sq_eq_one (hk : 4 ≤ k) :
    Nat.card {g : OtherDihedralGroup k // g ^ 2 = 1} = 4 := by
  have : NeZero (2 ^ (k - 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h2 : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
  have hunit : IsUnit ((2 ^ (k - 3) + 1 : ℕ) : ZMod (2 ^ (k - 1))) := by
    refine (ZMod.unitOfCoprime _ ((Nat.coprime_two_right.mpr ?_).pow_right _)).isUnit
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hiff (x : ZMod (2 ^ (k - 1))) :
      (1 + (otherDihedralUnit k : ZMod (2 ^ (k - 1)))) * x = 0 ↔ 2 * x = 0 := by
    rw [show (1 + (otherDihedralUnit k : ZMod (2 ^ (k - 1)))) =
      ((2 ^ (k - 3) + 1 : ℕ) : ZMod (2 ^ (k - 1))) * 2 by
        simp only [otherDihedralUnit, Units.val_mkOfMulEqOne]
        push_cast
        rw [show k - 2 = k - 3 + 1 by omega, pow_succ]
        ring1, mul_assoc, hunit.mul_right_eq_zero]
  rw [card_sq_eq_one_semidirectProduct, ZMod.card_two_mul_eq_zero h2,
    Nat.card_congr (Equiv.subtypeEquivRight hiff), ZMod.card_two_mul_eq_zero h2]

/-- **`D_{2^{k-1}}` and `Q_{2^k}` are not isomorphic** (LMFDB `group.semi_dihedral`,
`group.other_dihedral`): they have `2 ^ (k - 1) + 2` and `2` solutions of `g² = 1`. -/
lemma DihedralGroup.isEmpty_mulEquiv_quaternionGroup :
    IsEmpty (DihedralGroup (2 ^ (k - 1)) ≃* QuaternionGroup (2 ^ (k - 2))) := by
  have hk : 3 ≤ k := Fact.out
  have : NeZero (2 ^ (k - 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  refine ⟨fun f ↦ absurd f.card_sq_eq_one ?_⟩
  rw [card_sq_eq_one (dvd_pow_self 2 (by omega)), QuaternionGroup.card_sq_eq_one]
  omega

/-- **`D_{2^{k-1}}` and `SD_{2^k}` are not isomorphic** (LMFDB `group.semi_dihedral`,
`group.other_dihedral`): they have `2 ^ (k - 1) + 2` and `2 ^ (k - 2) + 2` solutions of
`g² = 1`. -/
lemma DihedralGroup.isEmpty_mulEquiv_semiDihedralGroup :
    IsEmpty (DihedralGroup (2 ^ (k - 1)) ≃* SemiDihedralGroup k) := by
  have hk : 3 ≤ k := Fact.out
  have : NeZero (2 ^ (k - 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hlt : 2 ^ (k - 2) < 2 ^ (k - 1) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : k - 2 < k - 1)
  refine ⟨fun f ↦ absurd f.card_sq_eq_one ?_⟩
  rw [card_sq_eq_one (dvd_pow_self 2 (by omega)), SemiDihedralGroup.card_sq_eq_one]
  omega

/-- **`D_{2^{k-1}}` and `OD_{2^k}` are not isomorphic for `k ≥ 4`** (LMFDB `group.semi_dihedral`,
`group.other_dihedral`): they have `2 ^ (k - 1) + 2` and `4` solutions of `g² = 1`. -/
lemma DihedralGroup.isEmpty_mulEquiv_otherDihedralGroup (hk : 4 ≤ k) :
    IsEmpty (DihedralGroup (2 ^ (k - 1)) ≃* OtherDihedralGroup k) := by
  have : NeZero (2 ^ (k - 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h4 : 2 ^ 2 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right two_pos (by omega : 2 ≤ k - 1)
  refine ⟨fun f ↦ absurd f.card_sq_eq_one ?_⟩
  rw [card_sq_eq_one (dvd_pow_self 2 (by omega)), OtherDihedralGroup.card_sq_eq_one hk]
  omega

/-- **`Q_{2^k}` and `SD_{2^k}` are not isomorphic** (LMFDB `group.semi_dihedral`,
`group.other_dihedral`): they have `2` and `2 ^ (k - 2) + 2` solutions of `g² = 1`. -/
lemma QuaternionGroup.isEmpty_mulEquiv_semiDihedralGroup :
    IsEmpty (QuaternionGroup (2 ^ (k - 2)) ≃* SemiDihedralGroup k) := by
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h1 : 1 ≤ 2 ^ (k - 2) := Nat.one_le_two_pow
  refine ⟨fun f ↦ absurd f.card_sq_eq_one ?_⟩
  rw [card_sq_eq_one, SemiDihedralGroup.card_sq_eq_one]
  omega

/-- **`Q_{2^k}` and `OD_{2^k}` are not isomorphic for `k ≥ 4`** (LMFDB `group.semi_dihedral`,
`group.other_dihedral`): they have `2` and `4` solutions of `g² = 1`. -/
lemma QuaternionGroup.isEmpty_mulEquiv_otherDihedralGroup (hk : 4 ≤ k) :
    IsEmpty (QuaternionGroup (2 ^ (k - 2)) ≃* OtherDihedralGroup k) := by
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  refine ⟨fun f ↦ absurd f.card_sq_eq_one ?_⟩
  rw [card_sq_eq_one, OtherDihedralGroup.card_sq_eq_one hk]
  omega

/-- **`SD_{2^k}` and `OD_{2^k}` are not isomorphic for `k ≥ 4`** (LMFDB `group.semi_dihedral`,
`group.other_dihedral`): they have `2 ^ (k - 2) + 2` and `4` solutions of `g² = 1`. -/
lemma SemiDihedralGroup.isEmpty_mulEquiv_otherDihedralGroup (hk : 4 ≤ k) :
    IsEmpty (SemiDihedralGroup k ≃* OtherDihedralGroup k) := by
  have h4 : 2 ^ 2 ≤ 2 ^ (k - 2) := Nat.pow_le_pow_right two_pos (by omega : 2 ≤ k - 2)
  refine ⟨fun f ↦ absurd f.card_sq_eq_one ?_⟩
  rw [card_sq_eq_one, OtherDihedralGroup.card_sq_eq_one hk]
  omega
