import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.Linarith
import LeanBridge.ForMathlib.GroupTheory.Complete

/-!
# The automorphisms of the symmetric groups

An automorphism of the symmetric group `S_n` sends a transposition to an involution whose
centralizer has the same order `2 (n - 2)!`. A product of `k` disjoint transpositions has a
centralizer of order `2 ^ k k! (n - 2k)!`, which is `2 (n - 2)!` only for `k = 1`, or for `k = 3`
and `n = 6`. So for `n ≠ 6` every automorphism of `S_n` sends transpositions to transpositions.

Such an automorphism `φ` is inner. Fix three points `a`, `b`, `c`. The transpositions `(a b)` and
`(a c)` do not commute, so neither do their images, which therefore move a common point `z`. Every
other `φ (a x)` moves `z` as well: otherwise, not commuting with `φ (a b)` and `φ (a c)`, it would
be the transposition of the other points of these two, which is
`φ (a b) φ (a c) φ (a b) = φ (b c)`. So `φ (a x)` is the transposition of `z` and
`π x = φ (a x) z`, the map `π` is a permutation, and `φ` agrees with conjugation by `π` on the
transpositions `(a x)`, hence on all transpositions, which generate `S_n`.

The centre of `S_n` is trivial for `n ≥ 3`, so `S_n` is complete for `n ≠ 2, 6`. For `n = 6` the
symmetric group has an outer automorphism, unique up to inner automorphisms
(`Equiv.Perm.outerAutFinSix`).

## Main results

* `Equiv.Perm.isSwap_mulAut_apply`: for `n ≠ 6`, every automorphism of `S_n` sends transpositions
  to transpositions.
* `Equiv.Perm.mem_range_conj_of_forall_isSwap`: an automorphism of `Perm α`, for a finite type
  `α`, that sends transpositions to transpositions is inner.
* `Equiv.Perm.surjective_conj_of_card_ne_six` (LMFDB `group.complete`, `nf.sextic_twin`): for
  `n ≠ 6`, every automorphism of `S_n` is inner.
* `Equiv.Perm.center_eq_bot`: for `n ≥ 3`, the centre of `S_n` is trivial.
* `Equiv.Perm.isComplete` (LMFDB `group.complete`): for `n ≠ 2, 6`, the symmetric group `S_n` is
  complete.

## References

* J. J. Rotman, *An Introduction to the Theory of Groups*, 4th ed., Graduate Texts in Mathematics
  148, Springer, 1995, chapter 7, for the completeness of `S_n`.
-/

open Nat Subgroup

namespace Equiv.Perm

variable {α : Type*} {φ : MulAut (Perm α)} {σ τ : Perm α} {a b c : α}

private lemma two_pow_mul_factorial_lt {j : ℕ} (hj : 2 ≤ j) :
    2 ^ (j + 1) * (j + 2)! < (2 * j + 2)! := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    rw [(by omega : 2 * (j + 1) + 2 = 2 * j + 2 + 1 + 1), factorial_succ (2 * j + 2 + 1),
      factorial_succ (2 * j + 2), (by omega : j + 1 + 2 = j + 2 + 1), factorial_succ (j + 2),
      pow_succ]
    nlinarith [Nat.mul_lt_mul_of_pos_left ih (by omega : 0 < 2 * (j + 3)),
      Nat.mul_le_mul_right (2 * j + 2)!
        (by nlinarith : 2 * (j + 3) ≤ (2 * j + 2 + 1 + 1) * (2 * j + 2 + 1))]

private lemma eq_one_of_factorial_mul_two_pow_eq {n k : ℕ} (hn : n ≠ 6) (hk : 1 ≤ k)
    (hkn : 2 * k ≤ n) (h : (n - 2 * k)! * 2 ^ k * k ! = (n - 2)! * 2) : k = 1 := by
  rcases Nat.exists_eq_add_of_le hkn with ⟨m, rfl⟩
  rw [Nat.add_sub_cancel_left] at h
  have hm : 0 < 2 * m ! := mul_pos two_pos (factorial_pos m)
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with hk1 | rfl | rfl | hk4
  · exact hk1
  · rw [(by omega : 2 * 2 + m - 2 = m + 1 + 1), factorial_succ (m + 1), factorial_succ m,
      factorial_two] at h
    have h5 : (m + 1 + 1) * (m + 1) = 4 :=
      Nat.eq_of_mul_eq_mul_right hm (by linarith)
    rcases m with _ | _ | m <;> nlinarith
  · have h6 : (3 : ℕ)! = 6 := rfl
    rw [(by omega : 2 * 3 + m - 2 = m + 1 + 1 + 1 + 1), factorial_succ (m + 1 + 1 + 1),
      factorial_succ (m + 1 + 1), factorial_succ (m + 1), factorial_succ m, h6] at h
    have h5 : (m + 1 + 1 + 1 + 1) * (m + 1 + 1 + 1) * (m + 1 + 1) * (m + 1) = 24 :=
      Nat.eq_of_mul_eq_mul_right hm (by linarith)
    rcases m with _ | m
    · omega
    · have : 5 * 4 * 3 * 2 ≤ (m + 1 + 1 + 1 + 1 + 1) * (m + 1 + 1 + 1 + 1) * (m + 1 + 1 + 1) *
          (m + 1 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega))
          (by omega)
      omega
  · rcases Nat.exists_eq_add_of_le' (by omega : 2 ≤ k) with ⟨j, rfl⟩
    rw [(by omega : 2 * (j + 2) + m - 2 = m + (2 * j + 2)), pow_succ] at h
    have hd : m ! * (2 * j + 2)! ≤ (m + (2 * j + 2))! :=
      Nat.le_of_dvd (factorial_pos _) (factorial_mul_factorial_dvd_factorial_add _ _)
    nlinarith [Nat.mul_lt_mul_of_pos_left (two_pow_mul_factorial_lt (by omega : 2 ≤ j))
      (factorial_pos m)]

private lemma centralizer_formula_replicate_two (n j : ℕ) (hj : j ≠ 0) :
    (n - (Multiset.replicate j 2).sum)! * (Multiset.replicate j 2).prod *
        ∏ m ∈ (Multiset.replicate j 2).toFinset, ((Multiset.replicate j 2).count m)! =
      (n - 2 * j)! * 2 ^ j * j ! := by
  rw [Multiset.sum_replicate, Multiset.prod_replicate, Multiset.toFinset_replicate,
    ite_eq_right hj, Finset.prod_singleton, Multiset.count_replicate_self, smul_eq_mul,
    mul_comm j 2]

lemma exists_apply_ne_and_apply_ne_of_not_commute (h : ¬Commute σ τ) : ∃ x, σ x ≠ x ∧ τ x ≠ x :=
  (not_forall.mp (mt Disjoint.commute h)).imp fun _ ↦ not_or.mp

variable (φ σ) in
lemma natCard_centralizer_mulAut_apply :
    Nat.card (centralizer {φ σ}) = Nat.card (centralizer {σ}) :=
  Nat.card_congr <| (φ.toEquiv.subtypeEquiv fun h ↦ by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact φ.injective.eq_iff.symm.trans (by rw [map_mul, map_mul]; rfl)).symm

variable [DecidableEq α]

lemma IsSwap.eq_swap_apply (hσ : σ.IsSwap) {x : α} (hx : σ x ≠ x) : σ = swap x (σ x) := by
  rcases hσ with ⟨a, b, -, rfl⟩
  rcases (swap_apply_ne_self_iff.mp hx).2 with rfl | rfl
  · rw [swap_apply_left]
  · rw [swap_apply_right, swap_comm]

lemma apply_ne_of_not_commute_swap {z w : α} (h : ¬Commute σ (swap z w)) (hz : σ z = z) :
    σ w ≠ w := by
  rcases exists_apply_ne_and_apply_ne_of_not_commute h with ⟨y, hy, hyw⟩
  rcases (swap_apply_ne_self_iff.mp hyw).2 with rfl | rfl
  · exact absurd hz hy
  · exact hy

lemma not_commute_swap_swap (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬Commute (swap a b) (swap a c) := by
  intro h
  have h' : (swap a b * swap a c) a = (swap a c * swap a b) a := DFunLike.congr_fun h.eq a
  rw [mul_apply, mul_apply, swap_apply_left, swap_apply_left,
    swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_of_ne_of_ne hab.symm hbc] at h'
  exact hbc h'.symm

lemma swap_mul_swap_mul_swap_eq (hac : a ≠ c) (hbc : b ≠ c) :
    swap a b * swap a c * swap a b = swap b c := by
  rw [swap_comm a c]
  exact swap_mul_swap_mul_swap hac.symm hbc.symm

variable [Fintype α]

/-- **For `n ≠ 6`, every automorphism of `S_n` sends transpositions to transpositions**: it sends
a transposition to an involution with a centralizer of the same order `2 (n - 2)!`, and a product
of `k` disjoint transpositions has a centralizer of order `2 ^ k k! (n - 2k)!`. -/
lemma isSwap_mulAut_apply (hα : Nat.card α ≠ 6) (hσ : σ.IsSwap) : (φ σ).IsSwap := by
  have hord : orderOf (φ σ) = 2 :=
    (orderOf_injective φ.toMonoidHom φ.injective σ).trans hσ.orderOf
  rcases cycleType_prime_order (hord ▸ Nat.prime_two) with ⟨k, hk⟩
  rw [hord] at hk
  have hle : 2 * (k + 1) ≤ Fintype.card α := by
    have h : (φ σ).cycleType.sum ≤ Fintype.card α :=
      (sum_cycleType (φ σ)).trans_le (Finset.card_le_univ _)
    rwa [hk, Multiset.sum_replicate, smul_eq_mul, mul_comm] at h
  have hc : Nat.card (centralizer {φ σ}) = Nat.card (centralizer {σ}) :=
    natCard_centralizer_mulAut_apply φ σ
  rw [nat_card_centralizer, nat_card_centralizer, hk, isSwap_iff_cycleType.mp hσ,
    ← Multiset.replicate_one, centralizer_formula_replicate_two _ _ k.succ_ne_zero,
    centralizer_formula_replicate_two _ _ one_ne_zero, mul_one, pow_one, factorial_one,
    mul_one] at hc
  rw [Nat.card_eq_fintype_card] at hα
  have hk1 : k + 1 = 1 := eq_one_of_factorial_mul_two_pow_eq hα (by omega) hle hc
  rw [isSwap_iff_cycleType, hk, (by omega : k = 0)]
  rfl

/-- **An automorphism of `Perm α` that sends transpositions to transpositions is inner.** Fix three
points `a`, `b`, `c`: the images of `(a b)` and `(a c)` move a common point `z`, so does every
`φ (a x)`, and `φ` is conjugation by the permutation `x ↦ φ (a x) z`. -/
lemma mem_range_conj_of_forall_isSwap (h : ∀ σ : Perm α, σ.IsSwap → (φ σ).IsSwap) :
    φ ∈ (MulAut.conj : Perm α →* MulAut (Perm α)).range := by
  rcases le_or_gt (Fintype.card α) 2 with hα | hα
  · refine ⟨1, MulEquiv.ext fun g ↦ ?_⟩
    rw [map_one, MulAut.one_apply]
    by_contra hg
    have hg1 : g ≠ 1 := fun h ↦ hg (h ▸ (map_one φ).symm)
    have hφg : φ g ≠ 1 := φ.map_ne_one_iff.mpr hg1
    have h2 : 2 < Fintype.card (Perm α) :=
      Fintype.two_lt_card_iff.mpr ⟨1, g, φ g, hg1.symm, hφg.symm, hg⟩
    rw [Fintype.card_perm] at h2
    exact absurd (h2.trans_le (factorial_le hα)) (by decide)
  rcases Fintype.two_lt_card_iff.mp hα with ⟨a, b, c, hab, hac, hbc⟩
  have hs (x : α) (hx : x ≠ a) : (φ (swap a x)).IsSwap := h _ ⟨a, x, hx.symm, rfl⟩
  have hnc (x y : α) (hx : x ≠ a) (hy : y ≠ a) (hxy : x ≠ y) :
      ¬Commute (φ (swap a x)) (φ (swap a y)) := fun hc ↦
    not_commute_swap_swap hx.symm hy.symm hxy (by simpa using hc.map φ.symm)
  rcases exists_apply_ne_and_apply_ne_of_not_commute (hnc b c hab.symm hac.symm hbc) with
    ⟨z, hzb, hzc⟩
  rcases (⟨_, (hs b hab.symm).eq_swap_apply hzb⟩ : ∃ w, φ (swap a b) = swap z w) with ⟨wb, hb⟩
  rcases (⟨_, (hs c hac.symm).eq_swap_apply hzc⟩ : ∃ w, φ (swap a c) = swap z w) with ⟨wc, hc⟩
  rw [hb, swap_apply_left] at hzb
  rw [hc, swap_apply_left] at hzc
  have hw : wb ≠ wc := fun h ↦ hbc (swap_injective_of_left a (φ.injective (by rw [hb, hc, h])))
  have hz (x : α) (hx : x ≠ a) : φ (swap a x) z ≠ z := by
    intro hxz
    have hxb : x ≠ b := by
      rintro rfl
      rw [hb, swap_apply_left] at hxz
      exact hzb hxz
    have hxc : x ≠ c := by
      rintro rfl
      rw [hc, swap_apply_left] at hxz
      exact hzc hxz
    have h1 : φ (swap a x) wb ≠ wb :=
      apply_ne_of_not_commute_swap (by rw [← hb]; exact hnc x b hx hab.symm hxb) hxz
    have h2 : φ (swap a x) wc ≠ wc :=
      apply_ne_of_not_commute_swap (by rw [← hc]; exact hnc x c hx hac.symm hxc) hxz
    rcases (⟨_, (hs x hx).eq_swap_apply h1⟩ : ∃ v, φ (swap a x) = swap wb v) with ⟨v, hv⟩
    rw [hv] at h2
    rcases (swap_apply_ne_self_iff.mp h2).2 with h3 | h3
    · exact hw h3.symm
    · have key : φ (swap a x) = φ (swap b c) := by
        rw [hv, ← swap_mul_swap_mul_swap_eq hac hbc, map_mul, map_mul, hb, hc,
          swap_mul_swap_mul_swap_eq hzc.symm hw, h3]
      have h5 : swap a x a = swap b c a := DFunLike.congr_fun (φ.injective key) a
      rw [swap_apply_left, swap_apply_of_ne_of_ne hab hac] at h5
      exact hx h5
  have hπ (x : α) : φ (swap a x) = swap z (φ (swap a x) z) := by
    rcases eq_or_ne x a with rfl | hx
    · rw [swap_self, ← one_def, map_one, one_apply, swap_self, one_def]
    · exact (hs x hx).eq_swap_apply (hz x hx)
  have hinj : Function.Injective fun x ↦ φ (swap a x) z := fun x y hxy ↦
    swap_injective_of_left a <| φ.injective <|
      (hπ x).trans <| (congrArg (swap z) hxy).trans (hπ y).symm
  rcases (⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), fun _ ↦ rfl⟩ :
    ∃ P : Perm α, ∀ x, P x = φ (swap a x) z) with ⟨P, hP⟩
  have hconj (x : α) : MulAut.conj P (swap a x) = φ (swap a x) := by
    rw [MulAut.conj_apply, ← swap_apply_apply, hP, hP, swap_self, ← one_def, map_one, one_apply]
    exact (hπ x).symm
  refine ⟨P, MulEquiv.toMonoidHom_injective <| MonoidHom.eq_of_eqOn_dense closure_isSwap ?_⟩
  rintro - ⟨x, y, hxy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom]
  rcases eq_or_ne x a with rfl | hx
  · exact hconj y
  rcases eq_or_ne y a with rfl | hy
  · rw [swap_comm]
    exact hconj x
  rw [← swap_mul_swap_mul_swap_eq hy.symm hxy, map_mul, map_mul, map_mul, map_mul, hconj, hconj]

/-- **For `n ≠ 6`, every automorphism of `S_n` is inner** (LMFDB `group.complete`,
`nf.sextic_twin`): it sends transpositions to transpositions (`Equiv.Perm.isSwap_mulAut_apply`), so
it is inner (`Equiv.Perm.mem_range_conj_of_forall_isSwap`). -/
lemma surjective_conj_of_card_ne_six (hα : Nat.card α ≠ 6) :
    Function.Surjective (MulAut.conj : Perm α →* MulAut (Perm α)) :=
  fun _ ↦ mem_range_conj_of_forall_isSwap fun _ ↦ isSwap_mulAut_apply hα

/-- **For `n ≥ 3`, the centre of `S_n` is trivial**: a permutation `g` moving a point `a`
does not commute with the transposition `(a c)` for a point `c` other than `a` and `g a`. -/
lemma center_eq_bot (hα : 3 ≤ Nat.card α) : center (Perm α) = ⊥ := by
  refine eq_bot_iff.mpr fun g hg ↦ mem_bot.mpr ?_
  by_contra hg1
  rcases not_forall.mp (mt Equiv.ext hg1) with ⟨a, ha⟩
  rw [one_apply] at ha
  have hcard : ({a, g a} : Finset α).card < (Finset.univ : Finset α).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact Finset.card_le_two.trans_lt hα
  rcases Finset.exists_mem_notMem_of_card_lt_card hcard with ⟨c, -, hc⟩
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have h1 : swap (g a) (g c) = swap a c := by
    rw [swap_apply_apply, (mem_center_iff.mp hg (swap a c)).symm, mul_inv_cancel_right]
  have h2 : swap (g a) (g c) (g a) = swap a c (g a) := DFunLike.congr_fun h1 (g a)
  rw [swap_apply_left, swap_apply_of_ne_of_ne ha (Ne.symm hc.2)] at h2
  exact hc.1 (g.injective h2)

/-- **The symmetric group `S_n` is complete for `n ≠ 2, 6`** (LMFDB `group.complete`): its centre
is trivial (`Equiv.Perm.center_eq_bot`, and `S_0`, `S_1` are trivial) and all its automorphisms
are inner (`Equiv.Perm.surjective_conj_of_card_ne_six`). -/
lemma isComplete (h2 : Nat.card α ≠ 2) (h6 : Nat.card α ≠ 6) : Group.IsComplete (Perm α) := by
  refine (Group.isComplete_iff _).mpr ⟨?_, surjective_conj_of_card_ne_six h6⟩
  rcases le_or_gt (Nat.card α) 1 with h1 | h3
  · have : Subsingleton α := Finite.card_le_one_iff_subsingleton.mp h1
    exact eq_bot_of_subsingleton _
  · exact center_eq_bot (by omega)

end Equiv.Perm
