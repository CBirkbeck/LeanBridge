import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import LeanBridge.ForMathlib.GroupTheory.OuterAutomorphism
import LeanBridge.ForMathlib.GroupTheory.Perm.MulAut

/-!
# The outer automorphism of the symmetric group `S₆`

The symmetric group `S_n` has an automorphism that is not inner only for `n = 6`. Such an
automorphism of `S₆` comes from the action of `S₆` on Sylvester's synthematic totals: a *syntheme*
is a partition of `{0, …, 5}` into three pairs, and a *total* is a set of five synthemes that
together contain each of the fifteen pairs once. There are six totals, and `S₆` permutes them. The
resulting homomorphism `S₆ → S₆` is injective, since its kernel is a normal subgroup without
`3`-cycles, so it is an automorphism `θ`; it sends the transposition `(0 1)` to the
fixed-point-free involution `(0 4)(1 2)(3 5)`, so it is not inner.

It is unique up to inner automorphisms. An automorphism `φ` of `S₆` sends `(0 1)` to an
involution whose centralizer has order `48`, a transposition or a product of three disjoint
transpositions. In the first case `φ` sends every transposition, a conjugate of `(0 1)`, to a
transposition, so it is inner (`Equiv.Perm.mem_range_conj_of_forall_isSwap`); in the second case
`θ ∘ φ` is in the first.

We label the totals `Tᵢ = (i 5) • T₅`, where `T₅` is the round-robin total whose synthemes are
`{{r, 5}, {r + 1, r - 1}, {r + 2, r - 2}}` for `r ∈ ℤ/5`. With this labelling `θ` is an involution.
Only the six totals `Tᵢ` and the fact that `S₆` permutes them are used, not that every total is one
of them.

## Main definitions

* `Equiv.Perm.synthematicTotal`: the synthematic totals `T₀, …, T₅`.
* `Equiv.Perm.outerAutFinSix` (LMFDB `nf.sextic_twin`): the outer automorphism `θ` of `S₆`, by
  which `σ ∈ S₆` acts on the indices of the totals: `T_{θ(σ)(i)} = σ • Tᵢ`.

## Main results

* `Equiv.Perm.synthematicTotal_outerAutFinSix_apply`: the defining property
  `T_{θ(σ)(i)} = σ • Tᵢ` of `θ`.
* `Equiv.Perm.isOuter_outerAutFinSix`: `θ` is not an inner automorphism.
* `Equiv.Perm.outerAutFinSix_outerAutFinSix`: `θ` is an involution.
* `Equiv.Perm.isPretransitive_map_stabilizer_outerAutFinSix`: `θ` sends the stabilizer of a point,
  a copy of `S₅`, to a transitive subgroup of `S₆`.
* `Equiv.Perm.mem_range_conj_of_isSwap`: an automorphism of `S₆` sending `(0 1)` to a
  transposition is inner.
* `Equiv.Perm.isSwap_or_isConj_apply_swap_zero_one`: an automorphism of `S₆` sends `(0 1)` to a
  transposition or to a product of three disjoint transpositions.
* `Equiv.Perm.exists_eq_outerAutFinSix_mul_conj`: the outer automorphisms of `S₆` are the
  composites of `θ` with inner automorphisms.
* `Equiv.Perm.natCard_out_fin_six`: the outer automorphism group of `S₆` has order `2`.
-/

open Finset

open scoped Pointwise

namespace Equiv.Perm

variable (σ : Perm (Fin 6)) (i : Fin 6) (φ : MulAut (Perm (Fin 6)))

/-- The **round-robin synthematic total** `T₅`: the five synthemes
`{{r, 5}, {r + 1, r - 1}, {r + 2, r - 2}}` for `r ∈ ℤ/5`, which together contain each pair of
elements of `Fin 6` once. A syntheme, a partition of `Fin 6` into three pairs, is the finset of its
pairs. -/
def roundRobinTotal : Finset (Finset (Finset (Fin 6))) :=
  {{{0, 5}, {1, 4}, {2, 3}}, {{1, 5}, {2, 0}, {3, 4}}, {{2, 5}, {3, 1}, {4, 0}},
    {{3, 5}, {4, 2}, {0, 1}}, {{4, 5}, {0, 3}, {1, 2}}}

/-- The **synthematic totals** `Tᵢ = (i 5) • T₅` for `i : Fin 6`, where `T₅` is the round-robin
total. These are Sylvester's six totals, the six partitions of the pairs of elements of `Fin 6`
into five synthemes. -/
def synthematicTotal : Finset (Finset (Finset (Fin 6))) :=
  swap i 5 • roundRobinTotal

lemma synthematicTotal_injective : Function.Injective synthematicTotal := by
  decide

/-- The finset of the six synthematic totals `Tᵢ`. -/
def synthematicTotals : Finset (Finset (Finset (Finset (Fin 6)))) :=
  univ.image synthematicTotal

lemma closure_finRotate_swap : Subgroup.closure {finRotate 6, swap 0 1} = ⊤ :=
  closure_cycle_adjacent_swap isCycle_finRotate support_finRotate 0

lemma smul_synthematicTotals : σ • synthematicTotals = synthematicTotals := by
  have h : Subgroup.closure {finRotate 6, swap 0 1} ≤
      MulAction.stabilizer (Perm (Fin 6)) synthematicTotals := by
    rw [Subgroup.closure_le]
    rintro τ (rfl | rfl) <;> rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] <;> decide
  rw [closure_finRotate_swap, top_le_iff] at h
  exact MulAction.mem_stabilizer_iff.mp (h ▸ Subgroup.mem_top σ)

/-- The six synthematic totals, as a set of finsets permuted by `Perm (Fin 6)`. -/
def synthematicTotalsSubMulAction :
    SubMulAction (Perm (Fin 6)) (Finset (Finset (Finset (Fin 6)))) where
  carrier := synthematicTotals
  smul_mem' τ _ hT := smul_synthematicTotals τ ▸ smul_mem_smul_finset hT

/-- The labelling `i ↦ Tᵢ` of the six synthematic totals. -/
noncomputable def synthematicTotalEquiv : Fin 6 ≃ synthematicTotalsSubMulAction :=
  Equiv.ofBijective (fun j ↦ ⟨synthematicTotal j, mem_image_of_mem _ (mem_univ j)⟩)
    ⟨fun _ _ h ↦ synthematicTotal_injective (congrArg Subtype.val h),
      fun T ↦ (mem_image.mp T.2).imp fun _ hi ↦ Subtype.ext hi.2⟩

/-- The homomorphism `S₆ → S₆` by which `σ` acts on the indices of the synthematic totals:
`T_{θ(σ)(i)} = σ • Tᵢ`. -/
noncomputable def outerAutFinSixHom : Perm (Fin 6) →* Perm (Fin 6) :=
  synthematicTotalEquiv.symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (Perm (Fin 6)) synthematicTotalsSubMulAction)

lemma synthematicTotal_outerAutFinSixHom_apply :
    synthematicTotal (outerAutFinSixHom σ i) = σ • synthematicTotal i :=
  congrArg Subtype.val (synthematicTotalEquiv.apply_symm_apply (σ • synthematicTotalEquiv i))

lemma outerAutFinSixHom_injective : Function.Injective outerAutFinSixHom := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra h
  have hA : alternatingGroup (Fin 6) ≤ outerAutFinSixHom.ker :=
    alternatingGroup_le_of_normal (by simp) ((Subgroup.nontrivial_iff_ne_bot _).mpr h)
  have hc : swap (0 : Fin 6) 1 * swap 0 2 ∈ outerAutFinSixHom.ker :=
    hA (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).mem_alternatingGroup
  have h0 : (swap (0 : Fin 6) 1 * swap 0 2) • synthematicTotal 0 = synthematicTotal 0 := by
    rw [← synthematicTotal_outerAutFinSixHom_apply, MonoidHom.mem_ker.mp hc, one_apply]
  exact (by decide : (swap (0 : Fin 6) 1 * swap 0 2) • synthematicTotal 0 ≠ synthematicTotal 0) h0

/-- The **outer automorphism** `θ` of `S₆` (LMFDB `nf.sextic_twin`): `σ ∈ S₆` permutes the six
synthematic totals `Tᵢ` as `θ(σ)` permutes their indices, `T_{θ(σ)(i)} = σ • Tᵢ`. It is not inner
(`isOuter_outerAutFinSix`) and is unique up to inner automorphisms
(`exists_eq_outerAutFinSix_mul_conj`); the LMFDB uses it to define twin sextic algebras. -/
noncomputable def outerAutFinSix : MulAut (Perm (Fin 6)) :=
  MulEquiv.ofBijective outerAutFinSixHom
    ⟨outerAutFinSixHom_injective, Finite.injective_iff_surjective.mp outerAutFinSixHom_injective⟩

/-- **The defining property of the outer automorphism `θ` of `S₆`**: `T_{θ(σ)(i)} = σ • Tᵢ`. -/
lemma synthematicTotal_outerAutFinSix_apply :
    synthematicTotal (outerAutFinSix σ i) = σ • synthematicTotal i :=
  synthematicTotal_outerAutFinSixHom_apply σ i

variable {σ i} in
lemma outerAutFinSix_apply_eq_of_smul {j : Fin 6}
    (h : σ • synthematicTotal i = synthematicTotal j) : outerAutFinSix σ i = j :=
  synthematicTotal_injective <| (synthematicTotal_outerAutFinSix_apply σ i).trans h

variable {σ} in
lemma outerAutFinSix_eq_of_forall {τ : Perm (Fin 6)}
    (h : ∀ j, σ • synthematicTotal j = synthematicTotal (τ j)) : outerAutFinSix σ = τ :=
  ext fun j ↦ outerAutFinSix_apply_eq_of_smul (h j)

lemma outerAutFinSix_finRotate : outerAutFinSix (finRotate 6) = swap 0 5 * swap 0 4 * swap 1 3 :=
  outerAutFinSix_eq_of_forall <| by decide

lemma outerAutFinSix_swap_zero_one : outerAutFinSix (swap 0 1) = swap 0 4 * swap 1 2 * swap 3 5 :=
  outerAutFinSix_eq_of_forall <| by decide

lemma outerAutFinSix_swap_mul_swap_mul_swap :
    outerAutFinSix (swap 0 4 * swap 1 2 * swap 3 5) = swap 0 1 :=
  outerAutFinSix_eq_of_forall <| by decide

/-- **The automorphism `θ` of `S₆` is outer**: it sends the transposition `(0 1)` to the
fixed-point-free involution `(0 4)(1 2)(3 5)`, while an inner automorphism sends it to a
transposition. -/
lemma isOuter_outerAutFinSix : outerAutFinSix.IsOuter := by
  rintro ⟨g, hg⟩
  have h : (swap 0 4 * swap 1 2 * swap 3 5 : Perm (Fin 6)) (g 2) = g 2 := by
    rw [← outerAutFinSix_swap_zero_one, ← hg, MulAut.conj_apply]
    simp [swap_apply_of_ne_of_ne]
  exact (by decide : ∀ x : Fin 6, (swap 0 4 * swap 1 2 * swap 3 5 : Perm (Fin 6)) x ≠ x) (g 2) h

/-- **The outer automorphism `θ` of `S₆` is an involution**: `θ(θ(σ)) = σ`. -/
lemma outerAutFinSix_outerAutFinSix : outerAutFinSix (outerAutFinSix σ) = σ := by
  have h : outerAutFinSix.toMonoidHom.comp outerAutFinSix.toMonoidHom = MonoidHom.id _ := by
    refine MonoidHom.eq_of_eqOn_dense closure_finRotate_swap ?_
    rintro τ (rfl | rfl)
    · exact (congrArg outerAutFinSix outerAutFinSix_finRotate).trans
        (outerAutFinSix_eq_of_forall <| by decide)
    · exact (congrArg outerAutFinSix outerAutFinSix_swap_zero_one).trans
        outerAutFinSix_swap_mul_swap_mul_swap
  exact DFunLike.congr_fun h σ

lemma outerAutFinSix_mul_self : outerAutFinSix * outerAutFinSix = 1 :=
  MulEquiv.ext outerAutFinSix_outerAutFinSix

/-- **The outer automorphism `θ` sends the stabilizer of a point, a copy of `S₅` in `S₆`, to a
transitive subgroup of `S₆`.** This transitive copy of `S₅` is the image of `PGL₂(𝔽₅)` acting on the
projective line over `𝔽₅` (`Equiv.Perm.map_stabilizer_outerAutFinSix`). -/
lemma isPretransitive_map_stabilizer_outerAutFinSix : MulAction.IsPretransitive
    ((MulAction.stabilizer (Perm (Fin 6)) (5 : Fin 6)).map outerAutFinSix.toMonoidHom) (Fin 6) := by
  have key (ν : Perm (Fin 6)) (k : Fin 6) (h5 : ν 5 = 5 := by decide)
      (hk : ν • synthematicTotal 0 = synthematicTotal k := by decide) :
      ∃ τ ∈ MulAction.stabilizer (Perm (Fin 6)) (5 : Fin 6), outerAutFinSix τ 0 = k :=
    ⟨ν, MulAction.mem_stabilizer_iff.mpr h5, outerAutFinSix_apply_eq_of_smul hk⟩
  have h (k : Fin 6) :
      ∃ τ ∈ MulAction.stabilizer (Perm (Fin 6)) (5 : Fin 6), outerAutFinSix τ 0 = k :=
    match k with
    | 0 => key 1 0
    | 1 => key (swap 0 4) 1
    | 2 => key (swap 0 3) 2
    | 3 => key (swap 0 2) 3
    | 4 => key (swap 0 1) 4
    | 5 => key (swap 1 4) 5
  refine ⟨fun i j ↦ ?_⟩
  rcases h i with ⟨σ, hσ, rfl⟩
  rcases h j with ⟨τ, hτ, rfl⟩
  refine ⟨⟨outerAutFinSix.toMonoidHom (τ * σ⁻¹),
    Subgroup.mem_map_of_mem _ (mul_mem hτ (inv_mem hσ))⟩, ?_⟩
  rw [Subgroup.smul_def]
  simp

private lemma cycleType_swap_zero_one : (swap (0 : Fin 6) 1).cycleType = {2} := by
  decide

private lemma cycleType_swap_mul_swap_mul_swap :
    (swap 0 4 * swap 1 2 * swap 3 5 : Perm (Fin 6)).cycleType = Multiset.replicate 3 2 := by
  decide

variable {φ} in
/-- **An automorphism of `S₆` sending the transposition `(0 1)` to a transposition is inner**: it
sends every transposition, a conjugate of `(0 1)`, to a transposition. -/
lemma mem_range_conj_of_isSwap (h : (φ (swap 0 1)).IsSwap) :
    φ ∈ (MulAut.conj : Perm (Fin 6) →* MulAut (Perm (Fin 6))).range := by
  refine mem_range_conj_of_forall_isSwap ?_
  rintro - ⟨x, y, hxy, rfl⟩
  rcases isConj_iff.mp (isConj_swap (by decide : (0 : Fin 6) ≠ 1) hxy) with ⟨g, hg⟩
  rcases h with ⟨a, b, hab, hφ⟩
  rw [← hg, map_mul, map_mul, map_inv, hφ, ← swap_apply_apply]
  exact ⟨_, _, (φ g).injective.ne hab, rfl⟩

/-- **An automorphism of `S₆` sends the transposition `(0 1)` to a transposition or to a conjugate
of `(0 4)(1 2)(3 5)`**: an involution whose centralizer has order `48`, as that of `(0 1)`. -/
lemma isSwap_or_isConj_apply_swap_zero_one :
    (φ (swap 0 1)).IsSwap ∨ IsConj (φ (swap 0 1)) (swap 0 4 * swap 1 2 * swap 3 5) := by
  have hord : orderOf (φ (swap 0 1)) = 2 :=
    (orderOf_injective φ.toMonoidHom φ.injective _).trans (orderOf_eq_prime (by decide) (by decide))
  rcases cycleType_prime_order (hord ▸ Nat.prime_two) with ⟨n, hn⟩
  rw [hord] at hn
  have hcard : Nat.card (Subgroup.centralizer {φ (swap 0 1)}) =
      Nat.card (Subgroup.centralizer {swap (0 : Fin 6) 1}) :=
    natCard_centralizer_mulAut_apply φ (swap 0 1)
  have hle : n ≤ 2 := by
    have h6 : (φ (swap 0 1)).cycleType.sum ≤ 6 := (sum_cycleType _).trans_le (card_le_univ _)
    rw [hn, Multiset.sum_replicate, smul_eq_mul] at h6
    omega
  rw [nat_card_centralizer, nat_card_centralizer, hn, cycleType_swap_zero_one] at hcard
  interval_cases n
  · left
    rw [← card_support_eq_two, ← sum_cycleType, hn]
    rfl
  · exact absurd hcard (by decide)
  · right
    exact isConj_iff_cycleType_eq.mpr (hn.trans cycleType_swap_mul_swap_mul_swap.symm)

variable {φ} in
/-- **The outer automorphism of `S₆` is unique up to inner automorphisms**: every outer
automorphism of `S₆` is `θ` composed with an inner automorphism. -/
lemma exists_eq_outerAutFinSix_mul_conj (hφ : φ.IsOuter) :
    ∃ g, φ = outerAutFinSix * MulAut.conj g := by
  rcases isSwap_or_isConj_apply_swap_zero_one φ with h | h
  · exact absurd (mem_range_conj_of_isSwap h) hφ
  rcases isConj_iff.mp h with ⟨g, hg⟩
  have hφg : φ (swap 0 1) = g⁻¹ * (swap 0 4 * swap 1 2 * swap 3 5) * g := by
    rw [← hg]
    group
  have hswap : ((outerAutFinSix * φ) (swap 0 1)).IsSwap := by
    rw [MulAut.mul_apply, hφg, map_mul, map_mul, outerAutFinSix_swap_mul_swap_mul_swap, map_inv]
    exact ⟨_, _, (outerAutFinSix g)⁻¹.injective.ne (by decide : (0 : Fin 6) ≠ 1),
      by rw [swap_apply_apply, inv_inv]⟩
  rcases mem_range_conj_of_isSwap hswap with ⟨k, hk⟩
  exact ⟨k, by rw [hk, ← mul_assoc, outerAutFinSix_mul_self, one_mul]⟩

/-- **The outer automorphism group of `S₆` has order `2`**, generated by the class of `θ`. -/
lemma natCard_out_fin_six : Nat.card (MulAut.Out (Perm (Fin 6))) = 2 := by
  refine Nat.card_eq_two_iff.mpr ⟨1, outerAutFinSix, ?_, Set.eq_univ_of_forall fun x ↦ ?_⟩
  · exact ((MulAut.isOuter_iff_ne_one _).mp isOuter_outerAutFinSix).symm
  induction x using QuotientGroup.induction_on with | H φ => ?_
  by_cases hφ : φ.IsOuter
  · rcases exists_eq_outerAutFinSix_mul_conj hφ with ⟨g, rfl⟩
    have hg : (MulAut.conj g : MulAut.Out (Perm (Fin 6))) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    right
    rw [Set.mem_singleton_iff, QuotientGroup.mk_mul, hg, mul_one]
  · left
    exact (QuotientGroup.eq_one_iff φ).mpr (not_not.mp hφ)

end Equiv.Perm
