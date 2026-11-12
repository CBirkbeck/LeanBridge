import LeanBridge.ForMathlib.GroupTheory.CompositionLength
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Perfect groups and their quotients

A group `G` is perfect (LMFDB `group.perfect`) if it equals its commutator subgroup. Equivalently,
`G` has no nontrivial abelian quotient, equivalently no nontrivial solvable quotient: a quotient of
a perfect group is perfect, a nontrivial perfect group is not solvable, and the abelianization of
`G` is a quotient by the commutator subgroup. For finite `G` this is also equivalent to having no
nontrivial cyclic quotient, since a nontrivial finite abelian group has a quotient of prime order.
The finiteness hypothesis cannot be dropped, as the knowl's text does: `(ℚ, +)` is not perfect, but
it has no nontrivial cyclic quotient, as it is divisible.

The knowl's example `SL(2, 5)` is perfect (Mathlib's `SL2.commutator_eq_top`) and has a cyclic
composition factor of order `2`, the centre `{±1}`; by the Jordan–Hölder theorem every
composition series of `SL(2, 5)` has a factor of order `2`.

Quotients are stated through surjective homomorphisms `G →* H`, to avoid choosing a normal
subgroup and an isomorphism.

## Main results

* `Group.isPerfect_iff_forall_commutative`, `Group.isPerfect_iff_forall_isSolvable` (LMFDB
  `group.perfect`): a group is perfect if and only if it has no nontrivial abelian quotient,
  equivalently no nontrivial solvable quotient.
* `Group.isPerfect_iff_forall_isCyclic` (LMFDB `group.perfect`): a finite group is perfect if and
  only if it has no nontrivial cyclic quotient.
* `Group.not_isPerfect_rat`, `Group.subsingleton_of_surjective_rat` (LMFDB `group.perfect`): `ℚ` is
  not perfect and has no nontrivial cyclic quotient.
* `Group.isPerfect_SL_two_five` (LMFDB `group.perfect`): `SL(2, 5)` is perfect.
* `Group.exists_isComposition_card_factor_eq_two_SL_two_five`,
  `Group.exists_card_factor_eq_two_SL_two_five` (LMFDB `group.perfect`): `SL(2, 5)` has a
  composition series with a factor of order `2`, and so does each of its composition series.
-/

universe u

open Subgroup

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

lemma exists_normal_le_isSimpleGroup_quotient (L : Subgroup G) [L.Normal] (hL : L ≠ ⊤) :
    ∃ (N : Subgroup G) (_ : N.Normal), L ≤ N ∧ IsSimpleGroup (G ⧸ N) := by
  rcases (Set.toFinite {N : Subgroup G | N.Normal ∧ L ≤ N ∧ N ≠ ⊤}).exists_le_maximal
    ⟨inferInstance, le_rfl, hL⟩ with ⟨N, -, ⟨hN, hLN, hNt⟩, hmax⟩
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNt
  refine ⟨N, hN, hLN, { eq_bot_or_eq_top_of_normal := fun M hM ↦ ?_ }⟩
  rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) M]
  by_cases hT : M.comap (QuotientGroup.mk' N) = ⊤
  · rw [hT, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    exact .inr rfl
  · have hNM : N ≤ M.comap (QuotientGroup.mk' N) :=
      (QuotientGroup.ker_mk' N).ge.trans (ker_le_comap _ M)
    have hle : M.comap (QuotientGroup.mk' N) ≤ N :=
      hmax ⟨hM.comap _, hLN.trans hNM, hT⟩ hNM
    exact .inl <| eq_bot_iff.mpr <| (map_mono hle).trans (QuotientGroup.map_mk'_self N).le

lemma exists_compositionSeries_head_eq_last_eq (H : Subgroup G) [H.Normal] (K : Subgroup G)
    (hHK : H ≤ K) :
    letI : JordanHolderLattice (Subgroup G) := jordanHolderLattice G
    ∃ s : CompositionSeries (Subgroup G), s.head = H ∧ s.last = K := by
  induction hn : Nat.card K using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    rcases eq_or_ne K H with rfl | hK
    · exact ⟨.singleton _ K, rfl, rfl⟩
    have hH : H.subgroupOf K ≠ ⊤ := fun h ↦
      hK (le_antisymm (subgroupOf_eq_top.mp h) hHK)
    rcases exists_normal_le_isSimpleGroup_quotient (H.subgroupOf K) hH with ⟨N, hN, hHN, hs⟩
    have hNK : (N.map K.subtype).subgroupOf K = N :=
      comap_map_eq_self_of_injective K.subtype_injective N
    have hlt : Nat.card (N.map K.subtype) < n := by
      rw [card_map_of_injective K.subtype_injective, ← hn, ← card_top (G := K)]
      exact card_lt_of_lt (QuotientGroup.nontrivial_iff.mp hs.toNontrivial).lt_top
    have hHN' : H ≤ N.map K.subtype := fun x hx ↦
      ⟨⟨x, hHK hx⟩, hHN (show ⟨x, hHK hx⟩ ∈ H.subgroupOf K from hx), rfl⟩
    rcases ih _ hlt _ hHN' rfl with ⟨s, hs₀, hs₁⟩
    refine ⟨s.snoc K ⟨hs₁ ▸ map_subtype_le N, ?_⟩, (s.head_snoc _ _).trans hs₀, s.last_snoc _ _⟩
    rw [hs₁, hNK]
    exact ⟨hN, hs⟩

end Subgroup

namespace Group

variable {G : Type u} [Group G]

/-- **A group is perfect if and only if it has no nontrivial abelian quotient** (LMFDB
`group.perfect`). -/
lemma isPerfect_iff_forall_commutative : IsPerfect G ↔ ∀ (H : Type u) [Group H] (f : G →* H),
    Function.Surjective f → (∀ a b : H, a * b = b * a) → Subsingleton H := by
  refine ⟨fun _ H _ f hf hH ↦ ?_, fun h ↦ ?_⟩
  · have : IsPerfect H := IsPerfect.ofSurjective hf
    rcases subsingleton_or_nontrivial H with h | h
    · exact h
    · exact (IsPerfect.not_isSolvable H (isSolvable_of_comm hH)).elim
  · refine isPerfect_def.mpr <| QuotientGroup.subsingleton_iff.mp ?_
    exact h (Abelianization G) Abelianization.of (QuotientGroup.mk_surjective) mul_comm

/-- **A group is perfect if and only if it has no nontrivial solvable quotient** (LMFDB
`group.perfect`). -/
lemma isPerfect_iff_forall_isSolvable : IsPerfect G ↔ ∀ (H : Type u) [Group H] [IsSolvable H]
    (f : G →* H), Function.Surjective f → Subsingleton H := by
  refine ⟨fun _ H _ _ f hf ↦ ?_, fun h ↦ isPerfect_iff_forall_commutative.mpr
    fun H _ f hf hH ↦ ?_⟩
  · have : IsPerfect H := IsPerfect.ofSurjective hf
    rcases subsingleton_or_nontrivial H with h | h
    · exact h
    · exact (IsPerfect.not_isSolvable H ‹_›).elim
  · have : IsSolvable H := isSolvable_of_comm hH
    exact h H f hf

/-- **A finite group is perfect if and only if it has no nontrivial cyclic quotient** (LMFDB
`group.perfect`). -/
lemma isPerfect_iff_forall_isCyclic [Finite G] : IsPerfect G ↔ ∀ (H : Type u) [Group H]
    [IsCyclic H] (f : G →* H), Function.Surjective f → Subsingleton H := by
  refine ⟨fun hG H _ _ f hf ↦ isPerfect_iff_forall_commutative.mp hG H f hf
    (IsCyclic.commGroup : CommGroup H).mul_comm, fun h ↦ ?_⟩
  refine isPerfect_def.mpr <| QuotientGroup.subsingleton_iff.mp ?_
  rcases subsingleton_or_nontrivial (Abelianization G) with hA | hA
  · exact hA
  have : Finite (Abelianization G) := inferInstanceAs (Finite (G ⧸ commutator G))
  rcases exists_normal_isSimpleGroup_quotient (G := Abelianization G) with ⟨N, hN, hs⟩
  have hc : Subsingleton (Abelianization G ⧸ N) := h _ ((QuotientGroup.mk' N).comp
    Abelianization.of) ((QuotientGroup.mk'_surjective N).comp QuotientGroup.mk_surjective)
  exact (not_subsingleton _ hc).elim

/-- **`ℚ` is not perfect** (LMFDB `group.perfect`): it is a nontrivial abelian group. -/
lemma not_isPerfect_rat : ¬IsPerfect (Multiplicative ℚ) := fun _ ↦
  IsPerfect.not_isSolvable _ (isSolvable_of_comm fun a b : Multiplicative ℚ ↦ mul_comm a b)

/-- **`ℚ` has no nontrivial cyclic quotient** (LMFDB `group.perfect`), as it is divisible: so the
characterisation of perfect groups by cyclic quotients needs finiteness. -/
lemma subsingleton_of_surjective_rat {H : Type*} [Group H] [IsCyclic H]
    (f : Multiplicative ℚ →* H) (hf : Function.Surjective f) : Subsingleton H := by
  rcases IsCyclic.exists_generator (α := H) with ⟨g, hg⟩
  rcases hf g with ⟨q, rfl⟩
  have hpow (n : ℕ) (hn : n ≠ 0) : ∃ m : ℤ, f q = f q ^ (m * n) := by
    rcases hg (f (.ofAdd (q.toAdd / n))) with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    simp only at hm
    rw [zpow_mul, hm, zpow_natCast, ← map_pow]
    congr 1
    apply Multiplicative.toAdd.injective
    simp [field]
  rcases hpow 2 two_ne_zero with ⟨m, hm⟩
  have hfin : IsOfFinOrder (f q) := by
    refine isOfFinOrder_iff_zpow_eq_one.mpr ⟨m * 2 - 1, by omega, ?_⟩
    rw [zpow_sub, zpow_one, mul_inv_eq_one]
    exact_mod_cast hm.symm
  rcases hpow (orderOf (f q)) hfin.orderOf_pos.ne' with ⟨m', hm'⟩
  have h₁ : f q = 1 := by
    rw [hm', mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨fun x y ↦ ?_⟩
  rcases hg x with ⟨a, rfl⟩
  rcases hg y with ⟨b, rfl⟩
  simp [h₁]

open Matrix SpecialLinearGroup

open scoped MatrixGroups

/-- **`SL(2, 5)` is perfect** (LMFDB `group.perfect`). -/
lemma isPerfect_SL_two_five : IsPerfect SL(2, ZMod 5) := by
  have h₁ : (2 : ZMod 5) ≠ 0 := by decide
  have h₂ : (2 : ZMod 5) ^ 2 ≠ 1 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact ⟨SL2.commutator_eq_top (F := ZMod 5) h₁ h₂⟩

private lemma normal_zpowers_neg_one : (zpowers (-1 : SL(2, ZMod 5))).Normal :=
  normal_of_le_center <| zpowers_le.mpr <| mem_center_iff.mpr fun g ↦ by
    rw [neg_one_mul, mul_neg_one]

private lemma card_zpowers_neg_one : Nat.card (zpowers (-1 : SL(2, ZMod 5))) = 2 := by
  rw [Nat.card_zpowers]
  refine orderOf_eq_prime (by simp) fun h ↦ ?_
  have h₁ : (-1 : ZMod 5) = 1 := by simpa using congrArg (fun A : SL(2, ZMod 5) ↦ A 0 0) h
  exact absurd h₁ (by decide +kernel)

/-- **`SL(2, 5)` has a composition series with a factor of order `2`** (LMFDB `group.perfect`): a
composition series through the centre `{±1}`. -/
lemma exists_isComposition_card_factor_eq_two_SL_two_five :
    ∃ s : SubnormalSeries SL(2, ZMod 5), s.IsComposition ∧ ∃ i, Nat.card (s.factor i) = 2 := by
  let _ : JordanHolderLattice (Subgroup SL(2, ZMod 5)) := jordanHolderLattice _
  have : (zpowers (-1 : SL(2, ZMod 5))).Normal := normal_zpowers_neg_one
  rcases exists_compositionSeries_head_eq_last_eq (zpowers (-1 : SL(2, ZMod 5))) ⊤ le_top with
    ⟨s, hs₀, hs₁⟩
  have hcard : Nat.card (zpowers (-1 : SL(2, ZMod 5)) ⧸
      (⊥ : Subgroup SL(2, ZMod 5)).subgroupOf (zpowers (-1))) = 2 := by
    rw [bot_subgroupOf, Nat.card_congr QuotientGroup.quotientBot.toEquiv, card_zpowers_neg_one]
  have hm : JordanHolderLattice.IsMaximal ⊥ s.head := by
    rw [hs₀]
    refine ⟨bot_le, by rw [bot_subgroupOf]; infer_instance, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isSimpleGroup_of_prime_card hcard
  let t : CompositionSeries (Subgroup SL(2, ZMod 5)) := s.cons ⊥ hm
  have key (A B : Subgroup SL(2, ZMod 5)) (hA : A = ⊥) (hB : B = zpowers (-1)) :
      Nat.card (B ⧸ A.subgroupOf B) = 2 := by
    subst hA hB
    exact hcard
  have h₀ : 0 < t.length := by
    dsimp [t, RelSeries.cons, RelSeries.append]
    omega
  refine ⟨⟨t.ofLE fun p hp ↦ ⟨hp.1, hp.2.1⟩, s.head_cons ⊥ hm, (s.last_cons ⊥ hm).trans hs₁⟩,
    fun i ↦ (t.step i).2.snd, ⟨⟨0, h₀⟩, key _ _ (s.head_cons ⊥ hm) ?_⟩⟩
  exact (s.cons_cast_succ ⊥ hm 0).trans hs₀

/-- **Every composition series of `SL(2, 5)` has a factor of order `2`** (LMFDB `group.perfect`),
by the Jordan–Hölder theorem: a perfect group may have cyclic composition factors. -/
lemma exists_card_factor_eq_two_SL_two_five {s : SubnormalSeries SL(2, ZMod 5)}
    (hs : s.IsComposition) : ∃ i, Nat.card (s.factor i) = 2 := by
  rcases exists_isComposition_card_factor_eq_two_SL_two_five with ⟨t, ht, i, hi⟩
  rcases ht.exists_equiv_nonempty_mulEquiv_factor hs with ⟨e, he⟩
  exact ⟨e i, (he i).elim fun φ ↦ (Nat.card_congr φ.toEquiv).symm.trans hi⟩

end Group
