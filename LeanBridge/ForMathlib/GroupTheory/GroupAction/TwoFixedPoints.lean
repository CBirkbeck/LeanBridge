import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer

/-!
# Finite groups acting with two fixed points

A finite subgroup of `PGL₂(ℂ)` acts on the projective line `ℙ¹(ℂ)` so that every nontrivial element
has exactly two fixed points and every point stabiliser is cyclic. This file classifies the finite
groups `G` with such an action on a set `X` (`MulAction.HasTwoFixedPoints`): `G` is cyclic,
dihedral of order `2n` with `n ≥ 2`, or isomorphic to `A₄`, `S₄` or `A₅`.

The proof is the classical one. The **poles** (`MulAction.poles`) are the points fixed by a
nontrivial element. Counting the pairs of a nontrivial element and a pole fixed by it (Burnside's
lemma on the poles), a group that fixes no point has exactly three orbits of poles, of sizes
`o₁, o₂, o₃` with `o₁ + o₂ + o₃ = |G| + 2`, and the orders of their stabilisers are `(2, 2, n)`,
`(2, 3, 3)`, `(2, 3, 4)` or `(2, 3, 5)`. The group is then identified in each case:

* `(2, 2, n)`: the stabiliser of a pole of the orbit of size `2` is cyclic of index two and every
  element outside it is an involution, so the group is dihedral;
* `(2, 3, 3)`: the group, of order `12`, acts faithfully on an orbit of size `4`, with image of
  index two in `S₄`, so it is `A₄`;
* `(2, 3, 4)`: the group, of order `24`, acts faithfully on its four Sylow `3`-subgroups, so it is
  `S₄`;
* `(2, 3, 5)`: the group, of order `60`, is simple, has five Sylow `2`-subgroups (Burnside's
  transfer theorem rules out fifteen) and acts faithfully on them, with image of index two in `S₅`,
  so it is `A₅`.

A normal subgroup `K` is controlled through the poles: the fixed points of its nontrivial elements,
at most `2 (|K| - 1)` of them, form a union of orbits of the group.

## Main definitions

* `MulAction.HasTwoFixedPoints`: every nontrivial element has exactly two fixed points and every
  point stabiliser is cyclic.
* `MulAction.poles`: the points fixed by a nontrivial element, as a sub-`G`-set.

## Main results

* `MulAction.HasTwoFixedPoints.exists_three_orbits`: a nontrivial group that fixes no point has
  three orbits of poles, whose sizes add up to the order of the group plus two.
* `MulAction.orbit_data`: the possible orders of the stabilisers of the three orbits.
* `DihedralGroup.nonempty_mulEquiv_of_index_eq_two`: a finite group with a cyclic subgroup of index
  two outside which every element is an involution is dihedral.
* `MulAction.HasTwoFixedPoints.nonempty_mulEquiv_alternatingGroup_four`,
  `MulAction.HasTwoFixedPoints.nonempty_mulEquiv_perm_four`,
  `MulAction.HasTwoFixedPoints.nonempty_mulEquiv_alternatingGroup_five`: the groups of orders `12`,
  `24` and `60` are `A₄`, `S₄` and `A₅`.
* `MulAction.HasTwoFixedPoints.card_eq_one_or_card_eq_sixty`: the group of order `60` is simple.
* `MulAction.HasTwoFixedPoints.classification`: the classification.
-/

open Equiv Set

namespace Sylow

variable {G : Type*} [Group G]

lemma card_eq_of_card_eq_mul {p a m : ℕ} [Fact p.Prime] [Finite G] (P : Sylow p G)
    (hG : Nat.card G = p ^ a * m) (hm : ¬p ∣ m) : Nat.card P = p ^ a := by
  have hm0 : m ≠ 0 := fun h ↦ hm (h ▸ dvd_zero p)
  rw [P.card_eq_multiplicity, hG, Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    hm0, Finsupp.add_apply, (Fact.out : p.Prime).factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

end Sylow

namespace DihedralGroup

variable {G : Type*} [Group G]

/-- **A finite group with a cyclic subgroup `C` of index two, outside which every element is an
involution, is the dihedral group of order `2 |C|`**: with `a` a generator of `C` and `b ∉ C`, the
relations `b² = 1` and `b x b = x⁻¹` for `x ∈ C` (as `(b x)² = 1`) make `r i ↦ aⁱ`, `sr i ↦ b aⁱ` an
injective homomorphism from the dihedral group, between groups of the same order. -/
lemma nonempty_mulEquiv_of_index_eq_two [Finite G] {C : Subgroup G} [IsCyclic C] (hC : C.index = 2)
    (h : ∀ g ∉ C, g ^ 2 = 1) : Nonempty (G ≃* DihedralGroup (Nat.card C)) := by
  rcases IsCyclic.exists_generator (α := C) with ⟨a, ha⟩
  rcases SetLike.exists_notMem_of_ne_top C fun hC' ↦ by simp [hC'] at hC with ⟨b, hbC⟩
  have : NeZero (Nat.card C) := ⟨Nat.card_pos.ne'⟩
  have hord : orderOf (a : G) = Nat.card C :=
    (Subgroup.orderOf_coe a).trans (orderOf_eq_card_of_forall_mem_zpowers ha)
  have hmod : ∀ k, (a : G) ^ (k % Nat.card C) = (a : G) ^ k := fun k ↦ hord ▸ pow_mod_orderOf _ k
  let f : ZMod (Nat.card C) → G := fun i ↦ (a : G) ^ i.val
  have hf : ∀ i j, f (i + j) = f i * f j := fun i j ↦ by
    simp only [f]
    rw [ZMod.val_add, hmod, pow_add]
  have hfC : ∀ i, f i ∈ C := fun i ↦ pow_mem a.2 _
  have hfneg : ∀ i, f (-i) = (f i)⁻¹ := fun i ↦ eq_inv_of_mul_eq_one_left <| by
    rw [← hf, neg_add_cancel]
    simp [f]
  have hbx : ∀ x ∈ C, b * x * b = x⁻¹ := fun x hx ↦ eq_inv_of_mul_eq_one_left <| by
    rw [mul_assoc, ← pow_two]
    exact h _ fun hbx ↦ hbC <| by simpa using C.mul_mem hbx (C.inv_mem hx)
  have hb2 : b * b = 1 := by
    rw [← pow_two]
    exact h b hbC
  let φ : DihedralGroup (Nat.card C) →* G := MonoidHom.mk' (fun
      | r i => f i
      | sr i => b * f i) <| by
    rintro (i | i) (j | j)
    · exact hf i j
    · simp only [r_mul_sr]
      rw [sub_eq_neg_add, hf, hfneg, ← hbx _ (hfC i), ← mul_assoc, ← mul_assoc, ← mul_assoc, hb2,
        one_mul, mul_assoc]
    · simp only [sr_mul_r]
      rw [hf, mul_assoc]
    · simp only [sr_mul_sr]
      rw [sub_eq_neg_add, hf, hfneg, ← hbx _ (hfC i), mul_assoc (b * f i)]
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr ?_
    rintro (i | i) hi
    · have hdvd : orderOf (a : G) ∣ i.val := orderOf_dvd_of_pow_eq_one (hi : f i = 1)
      rw [hord] at hdvd
      rw [one_def, (ZMod.val_eq_zero i).mp (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i))]
    · exact (hbC <| (eq_inv_of_mul_eq_one_left (hi : b * f i = 1)).symm ▸ C.inv_mem (hfC i)).elim
  have hcard : Nat.card G ≤ Nat.card (DihedralGroup (Nat.card C)) := by
    rw [nat_card, ← hC, C.index_mul_card]
  exact ⟨(MulEquiv.ofBijective φ (hφ.bijective_of_nat_card_le hcard)).symm⟩

end DihedralGroup

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X] {g : G} {x y y' y'' x₁ x₂ x₃ : X}
  {K : Subgroup G} {p : ℕ}

variable (G X) in
/-- An action of a group `G` on `X` **has two fixed points** if every nontrivial element of `G` has
exactly two fixed points and every point stabiliser is cyclic, as for the action of a finite
subgroup of `PGL₂(ℂ)` on the projective line. -/
structure HasTwoFixedPoints : Prop where
  /-- Every nontrivial element has exactly two fixed points. -/
  ncard_fixedBy : ∀ g : G, g ≠ 1 → (fixedBy X g).ncard = 2
  /-- Every point stabiliser is cyclic. -/
  isCyclic_stabilizer : ∀ x : X, IsCyclic (stabilizer G x)

variable (G X) in
/-- The **poles** of an action of `G` on `X`: the points fixed by a nontrivial element of `G`, as a
`G`-stable subset of `X`. -/
def poles : SubMulAction G X where
  carrier := {x | ∃ g : G, g ≠ 1 ∧ g • x = x}
  smul_mem' g := by
    rintro x ⟨h, hh, hx⟩
    exact ⟨g * h * g⁻¹, conj_eq_one_iff.not.mpr hh, by simp [mul_smul, hx]⟩

lemma mem_poles : x ∈ poles G X ↔ ∃ g : G, g ≠ 1 ∧ g • x = x :=
  Iff.rfl

lemma HasTwoFixedPoints.finite_fixedBy (hG : HasTwoFixedPoints G X) (hg : g ≠ 1) :
    (fixedBy X g).Finite :=
  finite_of_ncard_ne_zero <| by simp [hG.ncard_fixedBy g hg]

lemma HasTwoFixedPoints.ncard_fixedBy_poles (hG : HasTwoFixedPoints G X) (hg : g ≠ 1) :
    (fixedBy (poles G X) g).ncard = 2 := by
  rw [← ncard_image_of_injective _ Subtype.val_injective, ← hG.ncard_fixedBy g hg]
  congr 1
  ext x
  refine ⟨?_, fun hx ↦ ⟨⟨x, g, hg, hx⟩, Subtype.ext hx, rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact congrArg Subtype.val hy

variable (x) in
lemma ncard_orbit_mul_card_stabilizer :
    (orbit G x).ncard * Nat.card (stabilizer G x) = Nat.card G :=
  index_stabilizer G x ▸ (stabilizer G x).index_mul_card

lemma card_stabilizer_eq_of_mem_orbit (hy : y ∈ orbit G x) :
    Nat.card (stabilizer G y) = Nat.card (stabilizer G x) := by
  rcases hy with ⟨g, rfl⟩
  rw [stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

lemma orbit_subset_iUnion_fixedBy (hK : K.Normal) (hg : g ∈ K) (hg1 : g ≠ 1) (hy : g • y = y) :
    orbit G y ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G) := by
  rintro _ ⟨a, rfl⟩
  refine mem_iUnion.mpr ⟨⟨⟨a * g * a⁻¹, hK.conj_mem g hg a⟩, fun h ↦ hg1 <| conj_eq_one_iff.mp <|
    congrArg Subtype.val h⟩, ?_⟩
  simp [mul_smul, hy]

/-- The **possible orbit data** of a finite group whose action has two fixed points: with orbits of
poles of sizes `o₁, o₂, o₃` and stabilisers of orders `n₁ ≤ n₂ ≤ n₃`, the products `oᵢ nᵢ` all equal
to the order `m = o₃ n₃` of the group and `o₁ + o₂ + o₃ = m + 2`, `(n₁, n₂, n₃)` is `(2, 2, n)`, or
`(2, 3, 3)`, `(2, 3, 4)` or `(2, 3, 5)` with `o₃` equal to `4`, `6` or `12` (and `m` to `12`, `24`
or `60`). -/
lemma orbit_data {o₁ o₂ o₃ n₁ n₂ n₃ : ℕ} (h₁ : o₁ * n₁ = o₃ * n₃) (h₂ : o₂ * n₂ = o₃ * n₃)
    (hn₁ : 2 ≤ n₁) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃) (h : o₁ + o₂ + o₃ = o₃ * n₃ + 2) :
    n₁ = 2 ∧ n₂ = 2 ∨ n₁ = 2 ∧ n₂ = 3 ∧
      (n₃ = 3 ∧ o₃ = 4 ∨ n₃ = 4 ∧ o₃ = 6 ∨ n₃ = 5 ∧ o₃ = 12) := by
  generalize hm : o₃ * n₃ = m at h₁ h₂ h
  have hn₁' : n₁ = 2 := by
    by_contra hne
    have h₁' : o₁ * 3 ≤ m := h₁ ▸ Nat.mul_le_mul_left o₁ (by omega)
    have h₂' : o₂ * 3 ≤ m := h₂ ▸ Nat.mul_le_mul_left o₂ (by omega)
    have h₃' : o₃ * 3 ≤ m := hm ▸ Nat.mul_le_mul_left o₃ (by omega)
    omega
  subst hn₁'
  have hn₂ : n₂ ≤ 3 := by
    by_contra hne
    have h₂' : o₂ * 4 ≤ m := h₂ ▸ Nat.mul_le_mul_left o₂ (by omega)
    have h₃' : o₃ * 4 ≤ m := hm ▸ Nat.mul_le_mul_left o₃ (by omega)
    omega
  interval_cases n₂
  · exact Or.inl ⟨rfl, rfl⟩
  · have hn₃ : n₃ < 6 := by
      by_contra hne
      have h₃' : o₃ * 6 ≤ m := hm ▸ Nat.mul_le_mul_left o₃ (by omega)
      omega
    interval_cases n₃ <;> omega

lemma HasTwoFixedPoints.pow_two_eq_one (hG : HasTwoFixedPoints G X)
    (hcov : ∀ y ∈ poles G X, y ∈ orbit G x₁ ∨ y ∈ orbit G x₂ ∨ y ∈ orbit G x₃)
    (hn₁ : Nat.card (stabilizer G x₁) = 2) (hn₂ : Nat.card (stabilizer G x₂) = 2)
    (hidx : (stabilizer G x₃).index = 2) (hg : g ∉ stabilizer G x₃) : g ^ 2 = 1 := by
  have hg1 : g ≠ 1 := fun h ↦ hg (h ▸ one_mem _)
  rcases nonempty_of_ncard_ne_zero (s := fixedBy X g) (by simp [hG.ncard_fixedBy g hg1]) with
    ⟨z, hz⟩
  have hpow : ∀ a : X, Nat.card (stabilizer G a) = 2 → z ∈ orbit G a → g ^ 2 = 1 := by
    intro a ha hza
    have h : (⟨g, hz⟩ : stabilizer G z) ^ Nat.card (stabilizer G z) = 1 := pow_card_eq_one'
    rw [card_stabilizer_eq_of_mem_orbit hza, ha] at h
    exact congrArg Subtype.val h
  rcases hcov z ⟨g, hg1, hz⟩ with h | h | ⟨k, rfl⟩
  · exact hpow x₁ hn₁ h
  · exact hpow x₂ hn₂ h
  · have hmem : k⁻¹ * g * k ∈ stabilizer G x₃ := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hz, inv_smul_smul]
    have h : k * (k⁻¹ * g * k) * k⁻¹ ∈ stabilizer G x₃ :=
      (Subgroup.normal_of_index_eq_two hidx).conj_mem _ hmem k
    rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] at h
    exact (hg h).elim

variable [Finite G]

lemma HasTwoFixedPoints.finite_poles (hG : HasTwoFixedPoints G X) : Finite (poles G X) :=
  Finite.to_subtype <| (finite_iUnion fun g : {g : G // g ≠ 1} ↦ hG.finite_fixedBy g.2).subset
    fun _ ⟨g, hg, hx⟩ ↦ mem_iUnion.mpr ⟨⟨g, hg⟩, hx⟩

lemma HasTwoFixedPoints.card_poles_add (hG : HasTwoFixedPoints G X) : Nat.card (poles G X) +
    2 * (Nat.card G - 1) = Nat.card (orbitRel.Quotient G (poles G X)) * Nat.card G := by
  classical
  have hfin : Finite (poles G X) := hG.finite_poles
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype (poles G X) := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient G (poles G X)) := Fintype.ofFinite _
  have h : ∑ g : G, Fintype.card (fixedBy (poles G X) g) =
      Fintype.card (orbitRel.Quotient G (poles G X)) * Fintype.card G :=
    sum_card_fixedBy_eq_card_orbits_mul_card_group G (poles G X)
  simp only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] at h
  rw [← h, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), fixedBy_one_eq_univ, ncard_univ,
    Finset.sum_congr rfl fun g hg ↦ hG.ncard_fixedBy_poles (Finset.ne_of_mem_erase hg),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, smul_eq_mul,
    mul_comm, Fintype.card_eq_nat_card]

lemma two_le_card_stabilizer (hx : x ∈ poles G X) : 2 ≤ Nat.card (stabilizer G x) := by
  rcases hx with ⟨g, hg, hx⟩
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr <| Subgroup.ne_bot_iff_exists_ne_one.mpr
    ⟨⟨g, hx⟩, fun h ↦ hg (congrArg Subtype.val h)⟩

/-- **Orbit counting**: unless it fixes a point, a nontrivial finite group whose action has two
fixed points has three poles whose orbits cover the poles and have sizes adding up to the order of
the group plus two. By Burnside's lemma on the poles, their number plus `2 (|G| - 1)` is `|G|` times
the number of orbits, and each orbit has size at least `2` and at most `|G| / 2`, so there are
exactly three orbits of poles. -/
lemma HasTwoFixedPoints.exists_three_orbits [Nontrivial G] (hG : HasTwoFixedPoints G X)
    (hX : ∀ x : X, stabilizer G x ≠ ⊤) : ∃ x₁ x₂ x₃ : X, x₁ ∈ poles G X ∧ x₂ ∈ poles G X ∧
      x₃ ∈ poles G X ∧ (∀ y ∈ poles G X, y ∈ orbit G x₁ ∨ y ∈ orbit G x₂ ∨ y ∈ orbit G x₃) ∧
      (orbit G x₁).ncard + (orbit G x₂).ncard + (orbit G x₃).ncard = Nat.card G + 2 := by
  classical
  have hfin : Finite (poles G X) := hG.finite_poles
  let _ : Fintype (poles G X) := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient G (poles G X)) := Fintype.ofFinite _
  have hsum : Nat.card (poles G X) =
      ∑ ω : orbitRel.Quotient G (poles G X), (orbit G (ω.out : X)).ncard := by
    rw [Nat.card_congr (selfEquivSigmaOrbits G (poles G X)), Nat.card_sigma]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Nat.card_coe_set_eq, ← SubMulAction.val_image_orbit,
      ncard_image_of_injective _ Subtype.val_injective]
  have hm : 2 ≤ Nat.card G := Finite.one_lt_card
  have ho : ∀ ω : orbitRel.Quotient G (poles G X), 2 ≤ (orbit G (ω.out : X)).ncard ∧
      2 * (orbit G (ω.out : X)).ncard ≤ Nat.card G := by
    intro ω
    have h : (orbit G (ω.out : X)).ncard * Nat.card (stabilizer G (ω.out : X)) = Nat.card G :=
      ncard_orbit_mul_card_stabilizer _
    have h₂ : 2 ≤ Nat.card (stabilizer G (ω.out : X)) := two_le_card_stabilizer ω.out.2
    have h₃ : Nat.card (stabilizer G (ω.out : X)) ≠ Nat.card G := fun h' ↦
      hX _ <| Subgroup.eq_top_of_card_eq _ h'
    refine ⟨?_, h ▸ (mul_comm 2 _).trans_le (Nat.mul_le_mul_left _ h₂)⟩
    have h₀ : (orbit G (ω.out : X)).ncard ≠ 0 := fun h₀ ↦ by
      rw [h₀, zero_mul] at h
      omega
    have h₁ : (orbit G (ω.out : X)).ncard ≠ 1 := fun h₁ ↦ h₃ <| by rwa [h₁, one_mul] at h
    omega
  have hle :
      2 * Nat.card (poles G X) ≤ Fintype.card (orbitRel.Quotient G (poles G X)) * Nat.card G := by
    rw [hsum, Finset.mul_sum, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun ω _ ↦ (ho ω).2
  have hge : 2 * Fintype.card (orbitRel.Quotient G (poles G X)) ≤ Nat.card (poles G X) := by
    rw [hsum, mul_comm, ← smul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun ω _ ↦ (ho ω).1
  have hc : Nat.card (poles G X) + 2 * (Nat.card G - 1) =
      Fintype.card (orbitRel.Quotient G (poles G X)) * Nat.card G :=
    hG.card_poles_add.trans <| by rw [Nat.card_eq_fintype_card]
  have hr : Fintype.card (orbitRel.Quotient G (poles G X)) = 3 := by
    have hr3 : Fintype.card (orbitRel.Quotient G (poles G X)) < 4 := by
      by_contra! h
      have h' : 4 * Nat.card G ≤ Fintype.card (orbitRel.Quotient G (poles G X)) * Nat.card G :=
        Nat.mul_le_mul_right _ h
      omega
    interval_cases hr : Fintype.card (orbitRel.Quotient G (poles G X)) <;> omega
  rcases Finset.card_eq_three.mp hr with ⟨ω₁, ω₂, ω₃, h₁₂, h₁₃, h₂₃, hω⟩
  refine ⟨ω₁.out, ω₂.out, ω₃.out, ω₁.out.2, ω₂.out.2, ω₃.out.2, fun y hy ↦ ?_, ?_⟩
  · have hmem : ⟦(⟨y, hy⟩ : poles G X)⟧ ∈ ({ω₁, ω₂, ω₃} : Finset _) := hω ▸ Finset.mem_univ _
    have hy' : (⟨y, hy⟩ : poles G X) ∈ orbit G (⟦(⟨y, hy⟩ : poles G X)⟧ :
        orbitRel.Quotient G (poles G X)).out :=
      mem_orbit_symm.mp (Quotient.mk_out (s := orbitRel G (poles G X)) ⟨y, hy⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> rw [h] at hy' <;> simp [SubMulAction.mem_orbit_subMul_iff.mp hy']
  · rw [hsum, hω, Finset.sum_insert (by simp [h₁₂, h₁₃]), Finset.sum_pair h₂₃, hr] at hc
    omega

/-- **A group of order `12` acting with two fixed points and with an orbit of size `4` is the
alternating group `A₄`**: it acts faithfully on that orbit, as a nontrivial element fixes only two
points, and the image is a subgroup of index two of the symmetric group `S₄`. -/
lemma HasTwoFixedPoints.nonempty_mulEquiv_alternatingGroup_four (hG : HasTwoFixedPoints G X)
    (hm : Nat.card G = 12) (ho : (orbit G x).ncard = 4) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
  have hfin : Finite (orbit G x) := (finite_range fun g : G ↦ g • x).to_subtype
  let _ : Fintype (orbit G x) := Fintype.ofFinite _
  let φ : G →* Perm (orbit G x) := toPermHom G (orbit G x)
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun g hg ↦ ?_
    by_contra hg1
    have hsub : orbit G x ⊆ fixedBy X g := fun y hy ↦ by
      simpa [φ, Subtype.ext_iff] using DFunLike.congr_fun hg ⟨y, hy⟩
    have hle : (orbit G x).ncard ≤ (fixedBy X g).ncard :=
      ncard_le_ncard hsub (hG.finite_fixedBy hg1)
    rw [ho, hG.ncard_fixedBy g hg1] at hle
    omega
  have hcard : Nat.card (orbit G x) = 4 := (Nat.card_coe_set_eq _).trans ho
  have hidx : φ.range.index = 2 := by
    have h : φ.range.index * Nat.card φ.range = Nat.card (Perm (orbit G x)) :=
      φ.range.index_mul_card
    rw [Nat.card_perm, hcard, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hm] at h
    norm_num [Nat.factorial] at h
    omega
  exact ⟨(MonoidHom.ofInjective hφ).trans <| (MulEquiv.subgroupCongr
    (Perm.eq_alternatingGroup_of_index_eq_two hidx)).trans
      (altCongrHom (Finite.equivFinOfCardEq hcard))⟩

variable (K) in
lemma HasTwoFixedPoints.finite_iUnion_fixedBy (hG : HasTwoFixedPoints G X) :
    (⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G)).Finite :=
  finite_iUnion fun k ↦ hG.finite_fixedBy fun h ↦ k.2 (Subtype.ext h)

variable (K) in
lemma HasTwoFixedPoints.ncard_iUnion_fixedBy_le (hG : HasTwoFixedPoints G X) :
    (⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G)).ncard ≤ 2 * (Nat.card K - 1) := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  refine (ncard_iUnion_le_of_fintype _).trans_eq ?_
  rw [Finset.sum_congr rfl fun k _ ↦ hG.ncard_fixedBy _ fun h ↦ k.2 (Subtype.ext h),
    Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, mul_comm, Nat.card_eq_fintype_card]

lemma HasTwoFixedPoints.exists_dvd_card_stabilizer [Fact p.Prime] (hG : HasTwoFixedPoints G X)
    (hK : K.Normal) (hp : p ∣ Nat.card K) : ∃ y ∈ poles G X, p ∣ Nat.card (stabilizer G y) ∧
      orbit G y ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G) := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  rcases exists_prime_orderOf_dvd_card p (Nat.card_eq_fintype_card (α := K) ▸ hp) with ⟨k, hk⟩
  have hk1 : (k : G) ≠ 1 := fun h ↦ (Fact.out : p.Prime).one_lt.ne' <| by
    rw [← hk, ← Subgroup.orderOf_coe, h, orderOf_one]
  rcases nonempty_of_ncard_ne_zero (s := fixedBy X (k : G)) (by simp [hG.ncard_fixedBy _ hk1])
    with ⟨y, hy⟩
  refine ⟨y, ⟨k, hk1, hy⟩, ?_, orbit_subset_iUnion_fixedBy hK k.2 hk1 hy⟩
  rw [← hk, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk (k : G) (mem_stabilizer_iff.mpr hy)]
  exact orderOf_dvd_natCard _

lemma HasTwoFixedPoints.ncard_orbit_le (hG : HasTwoFixedPoints G X)
    (h : orbit G y ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G)) :
    (orbit G y).ncard ≤ 2 * (Nat.card K - 1) :=
  (ncard_le_ncard h (hG.finite_iUnion_fixedBy K)).trans (hG.ncard_iUnion_fixedBy_le K)

lemma HasTwoFixedPoints.ncard_orbit_add_ncard_orbit_le (hG : HasTwoFixedPoints G X)
    (h : orbit G y ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G))
    (h' : orbit G y' ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G))
    (hne : Nat.card (stabilizer G y) ≠ Nat.card (stabilizer G y')) :
    (orbit G y).ncard + (orbit G y').ncard ≤ 2 * (Nat.card K - 1) := by
  rw [← ncard_union_eq (disjoint_left.mpr fun z hz hz' ↦ hne <|
    (card_stabilizer_eq_of_mem_orbit hz).symm.trans (card_stabilizer_eq_of_mem_orbit hz'))
    (finite_range _) (finite_range _)]
  exact (ncard_le_ncard (union_subset h h') (hG.finite_iUnion_fixedBy K)).trans
    (hG.ncard_iUnion_fixedBy_le K)

lemma HasTwoFixedPoints.ncard_orbit_add_ncard_orbit_add_ncard_orbit_le (hG : HasTwoFixedPoints G X)
    (h : orbit G y ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G))
    (h' : orbit G y' ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G))
    (h'' : orbit G y'' ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G))
    (hne : Nat.card (stabilizer G y) ≠ Nat.card (stabilizer G y'))
    (hne' : Nat.card (stabilizer G y) ≠ Nat.card (stabilizer G y''))
    (hne'' : Nat.card (stabilizer G y') ≠ Nat.card (stabilizer G y'')) :
    (orbit G y).ncard + (orbit G y').ncard + (orbit G y'').ncard ≤ 2 * (Nat.card K - 1) := by
  have hdisj : ∀ {a b : X}, Nat.card (stabilizer G a) ≠ Nat.card (stabilizer G b) →
      Disjoint (orbit G a) (orbit G b) := fun hab ↦ disjoint_left.mpr fun z hz hz' ↦ hab <|
    (card_stabilizer_eq_of_mem_orbit hz).symm.trans (card_stabilizer_eq_of_mem_orbit hz')
  rw [← ncard_union_eq (hdisj hne) (finite_range _) (finite_range _),
    ← ncard_union_eq (disjoint_union_left.mpr ⟨hdisj hne', hdisj hne''⟩)
      ((finite_range _).union (finite_range _)) (finite_range _)]
  exact (ncard_le_ncard (union_subset (union_subset h h') h'') (hG.finite_iUnion_fixedBy K)).trans
    (hG.ncard_iUnion_fixedBy_le K)

/-- **A group of order `24` acting with two fixed points, with stabilisers of poles of order `2`,
`3` or `4`, is the symmetric group `S₄`**: it acts faithfully on its four Sylow `3`-subgroups. A
nontrivial element of the kernel would have its fixed points in an orbit of size at least `6`, and
the kernel, a normal subgroup of order dividing `6`, is too small for that. -/
lemma HasTwoFixedPoints.nonempty_mulEquiv_perm_four (hG : HasTwoFixedPoints G X)
    (hm : Nat.card G = 24) (hX : ∀ y ∈ poles G X, Nat.card (stabilizer G y) = 2 ∨
      Nat.card (stabilizer G y) = 3 ∨ Nat.card (stabilizer G y) = 4) :
    Nonempty (G ≃* Perm (Fin 4)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : ∀ y : X, (orbit G y).ncard * Nat.card (stabilizer G y) = 24 := fun y ↦
    hm ▸ ncard_orbit_mul_card_stabilizer y
  have h3 : ∀ K : Subgroup G, K.Normal → 3 ∣ Nat.card K → 5 ≤ Nat.card K := by
    intro K hK h3K
    rcases hG.exists_dvd_card_stabilizer hK h3K with ⟨y, hy, hdvd, hsub⟩
    have hle : (orbit G y).ncard ≤ 2 * (Nat.card K - 1) := hG.ncard_orbit_le hsub
    have hoy : (orbit G y).ncard * Nat.card (stabilizer G y) = 24 := ho y
    rcases hX y hy with h | h | h <;> rw [h] at hdvd hoy <;> omega
  have h2 : ∀ K : Subgroup G, K.Normal → 2 ∣ Nat.card K → 4 ≤ Nat.card K := by
    intro K hK h2K
    rcases hG.exists_dvd_card_stabilizer hK h2K with ⟨y, hy, hdvd, hsub⟩
    have hle : (orbit G y).ncard ≤ 2 * (Nat.card K - 1) := hG.ncard_orbit_le hsub
    have hoy : (orbit G y).ncard * Nat.card (stabilizer G y) = 24 := ho y
    rcases hX y hy with h | h | h <;> rw [h] at hdvd hoy <;> omega
  have h6 : ∀ K : Subgroup G, K.Normal → Nat.card K ≠ 6 := by
    intro K hK h6K
    rcases hG.exists_dvd_card_stabilizer hK (p := 2) (by rw [h6K]; norm_num) with
      ⟨y, hy, hdvd, hsub⟩
    rcases hG.exists_dvd_card_stabilizer hK (p := 3) (by rw [h6K]; norm_num) with
      ⟨y', hy', hdvd', hsub'⟩
    have hoy : (orbit G y).ncard * Nat.card (stabilizer G y) = 24 := ho y
    have hoy' : (orbit G y').ncard * Nat.card (stabilizer G y') = 24 := ho y'
    rcases hX y hy with h | h | h <;> rw [h] at hdvd hoy <;>
      rcases hX y' hy' with h' | h' | h' <;> rw [h'] at hdvd' hoy' <;> try omega
    all_goals
      have hle : (orbit G y).ncard + (orbit G y').ncard ≤ 2 * (Nat.card K - 1) :=
        hG.ncard_orbit_add_ncard_orbit_le hsub hsub' (by rw [h, h']; omega)
      omega
  rcases (inferInstance : Nonempty (Sylow 3 G)) with ⟨P⟩
  have hP : Nat.card P = 3 := by
    simpa using P.card_eq_of_card_eq_mul (a := 1) (m := 8) (by rw [hm]; norm_num) (by norm_num)
  have hPi : P.index = 8 := by
    have h : (P : Subgroup G).index * Nat.card P = Nat.card G := P.index_mul_card
    rw [hP, hm] at h
    omega
  have hn : Nat.card (Sylow 3 G) = 4 := by
    have hmod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
    have hdvd : Nat.card (Sylow 3 G) ∣ 8 := hPi ▸ P.card_dvd_index
    have hn1 : Nat.card (Sylow 3 G) ≠ 1 := fun hn1 ↦ by
      have : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp hn1).1
      have h5 : 5 ≤ Nat.card P := h3 P P.normal_of_subsingleton (by rw [hP])
      omega
    have hle : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (Sylow 3 G) <;> simp_all [Nat.ModEq]
  have hN : Nat.card (Subgroup.normalizer (P : Set G)) = 6 := by
    have h : (Subgroup.normalizer (P : Set G)).index * Nat.card (Subgroup.normalizer (P : Set G)) =
        Nat.card G :=
      (Subgroup.normalizer (P : Set G)).index_mul_card
    rw [← P.card_eq_index_normalizer, hn, hm] at h
    omega
  let φ : G →* Perm (Sylow 3 G) := toPermHom G (Sylow 3 G)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_card]
    have hle : φ.ker ≤ Subgroup.normalizer (P : Set G) := fun g hg ↦
      Sylow.smul_eq_iff_mem_normalizer.mp (DFunLike.congr_fun hg P)
    have hdvd : Nat.card φ.ker ∣ 6 := hN ▸ Subgroup.card_dvd_of_le hle
    have hle6 : Nat.card φ.ker ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    interval_cases h : Nat.card φ.ker
    · rfl
    · exact absurd (h2 _ φ.normal_ker (by rw [h])) (by rw [h]; norm_num)
    · exact absurd (h3 _ φ.normal_ker (by rw [h])) (by rw [h]; norm_num)
    · exact absurd hdvd (by norm_num)
    · exact absurd hdvd (by norm_num)
    · exact absurd h (h6 _ φ.normal_ker)
  have hcard : Nat.card (Perm (Sylow 3 G)) ≤ Nat.card G := by
    rw [Nat.card_perm, hn, hm]
    rfl
  exact ⟨(MulEquiv.ofBijective φ (hφ.bijective_of_nat_card_le hcard)).trans
    (permCongrHom (Finite.equivFinOfCardEq hn))⟩

lemma HasTwoFixedPoints.exists_card_stabilizer_eq (hG : HasTwoFixedPoints G X)
    (hX : ∀ y ∈ poles G X, Nat.card (stabilizer G y) = 2 ∨ Nat.card (stabilizer G y) = 3 ∨
      Nat.card (stabilizer G y) = 5) (hK : K.Normal) (hp : p = 2 ∨ p = 3 ∨ p = 5)
    (hpK : p ∣ Nat.card K) : ∃ y : X, Nat.card (stabilizer G y) = p ∧
      orbit G y ⊆ ⋃ k : {k : K // k ≠ 1}, fixedBy X ((k : K) : G) := by
  have : Fact p.Prime := ⟨by
    rcases hp with rfl | rfl | rfl
    exacts [Nat.prime_two, Nat.prime_three, Nat.prime_five]⟩
  rcases hG.exists_dvd_card_stabilizer hK hpK with ⟨y, hy, hdvd, hsub⟩
  refine ⟨y, ?_, hsub⟩
  rcases hX y hy with h | h | h <;> rw [h] at hdvd ⊢ <;> rcases hp with rfl | rfl | rfl <;> omega

/-- **A group of order `60` acting with two fixed points, with stabilisers of poles of order `2`,
`3` or `5`, is simple**: a normal subgroup `K` contains, for each prime `p` dividing its order, an
element of order `p`, a fixed point of which has a stabiliser of order `p` and an orbit of size
`60 / p` made of points fixed by nontrivial elements of `K`; there are at most `2 (|K| - 1)` of
those, which fails unless `|K|` is `1` or `60`. -/
lemma HasTwoFixedPoints.card_eq_one_or_card_eq_sixty (hG : HasTwoFixedPoints G X)
    (hm : Nat.card G = 60) (hX : ∀ y ∈ poles G X, Nat.card (stabilizer G y) = 2 ∨
      Nat.card (stabilizer G y) = 3 ∨ Nat.card (stabilizer G y) = 5) (hK : K.Normal) :
    Nat.card K = 1 ∨ Nat.card K = 60 := by
  have ho : ∀ y : X, (orbit G y).ncard * Nat.card (stabilizer G y) = 60 := fun y ↦
    hm ▸ ncard_orbit_mul_card_stabilizer y
  have h1 :
      ∀ p : ℕ, p = 2 ∨ p = 3 ∨ p = 5 → p ∣ Nat.card K → 60 ≤ p * (2 * (Nat.card K - 1)) := by
    intro p hp hpK
    rcases hG.exists_card_stabilizer_eq hX hK hp hpK with ⟨y, hyp, hsub⟩
    have hle : (orbit G y).ncard ≤ 2 * (Nat.card K - 1) := hG.ncard_orbit_le hsub
    have hoy : (orbit G y).ncard * p = 60 := hyp ▸ ho y
    nlinarith
  have h2 : ∀ p q : ℕ, p = 2 ∨ p = 3 ∨ p = 5 → q = 2 ∨ q = 3 ∨ q = 5 → p ≠ q → p ∣ Nat.card K →
      q ∣ Nat.card K → 60 * q + 60 * p ≤ p * q * (2 * (Nat.card K - 1)) := by
    intro p q hp hq hpq hpK hqK
    rcases hG.exists_card_stabilizer_eq hX hK hp hpK with ⟨y, hyp, hsub⟩
    rcases hG.exists_card_stabilizer_eq hX hK hq hqK with ⟨y', hyq, hsub'⟩
    have hle : (orbit G y).ncard + (orbit G y').ncard ≤ 2 * (Nat.card K - 1) :=
      hG.ncard_orbit_add_ncard_orbit_le hsub hsub' (by rw [hyp, hyq]; exact hpq)
    have hoy : (orbit G y).ncard * p = 60 := hyp ▸ ho y
    have hoy' : (orbit G y').ncard * q = 60 := hyq ▸ ho y'
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> omega
  have h3 : 2 ∣ Nat.card K → 3 ∣ Nat.card K → 5 ∣ Nat.card K → 32 ≤ Nat.card K := by
    intro h2K h3K h5K
    rcases hG.exists_card_stabilizer_eq hX hK (p := 2) (by norm_num) h2K with ⟨y, hy2, hsub⟩
    rcases hG.exists_card_stabilizer_eq hX hK (p := 3) (by norm_num) h3K with ⟨y', hy3, hsub'⟩
    rcases hG.exists_card_stabilizer_eq hX hK (p := 5) (by norm_num) h5K with ⟨y'', hy5, hsub''⟩
    have hle :
        (orbit G y).ncard + (orbit G y').ncard + (orbit G y'').ncard ≤ 2 * (Nat.card K - 1) :=
      hG.ncard_orbit_add_ncard_orbit_add_ncard_orbit_le hsub hsub' hsub''
        (by rw [hy2, hy3]; norm_num) (by rw [hy2, hy5]; norm_num) (by rw [hy3, hy5]; norm_num)
    have hoy : (orbit G y).ncard * 2 = 60 := hy2 ▸ ho y
    have hoy' : (orbit G y').ncard * 3 = 60 := hy3 ▸ ho y'
    have hoy'' : (orbit G y'').ncard * 5 = 60 := hy5 ▸ ho y''
    omega
  have h12 : 2 ∣ Nat.card K → 60 ≤ 2 * (2 * (Nat.card K - 1)) := h1 2 (by norm_num)
  have h13 : 3 ∣ Nat.card K → 60 ≤ 3 * (2 * (Nat.card K - 1)) := h1 3 (by norm_num)
  have h15 : 5 ∣ Nat.card K → 60 ≤ 5 * (2 * (Nat.card K - 1)) := h1 5 (by norm_num)
  have h23 : 2 ∣ Nat.card K → 3 ∣ Nat.card K → 60 * 3 + 60 * 2 ≤ 2 * 3 * (2 * (Nat.card K - 1)) :=
    h2 2 3 (by norm_num) (by norm_num) (by norm_num)
  have h25 : 2 ∣ Nat.card K → 5 ∣ Nat.card K → 60 * 5 + 60 * 2 ≤ 2 * 5 * (2 * (Nat.card K - 1)) :=
    h2 2 5 (by norm_num) (by norm_num) (by norm_num)
  have h35 : 3 ∣ Nat.card K → 5 ∣ Nat.card K → 60 * 5 + 60 * 3 ≤ 3 * 5 * (2 * (Nat.card K - 1)) :=
    h2 3 5 (by norm_num) (by norm_num) (by norm_num)
  have hmem : Nat.card K ∈ Nat.divisors 60 :=
    Nat.mem_divisors.mpr ⟨hm ▸ K.card_subgroup_dvd_card, by norm_num⟩
  rw [(by decide : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60})] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] at h12 h13 h15 h23 h25 h35 h3 ⊢ <;> omega

/-- **A group of order `60` acting with two fixed points, with stabilisers of poles of order `2`,
`3` or `5`, is the alternating group `A₅`**: it is simple, so by Burnside's transfer theorem it does
not have fifteen Sylow `2`-subgroups; it has five, and it acts faithfully on them, with image of
index two in `S₅`. -/
lemma HasTwoFixedPoints.nonempty_mulEquiv_alternatingGroup_five (hG : HasTwoFixedPoints G X)
    (hm : Nat.card G = 60) (hX : ∀ y ∈ poles G X, Nat.card (stabilizer G y) = 2 ∨
      Nat.card (stabilizer G y) = 3 ∨ Nat.card (stabilizer G y) = 5) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : ∀ K : Subgroup G, K.Normal → Nat.card K = 1 ∨ Nat.card K = 60 := fun _ hK ↦
    hG.card_eq_one_or_card_eq_sixty hm hX hK
  rcases (inferInstance : Nonempty (Sylow 2 G)) with ⟨P⟩
  have hP : Nat.card P = 4 := by
    simpa using P.card_eq_of_card_eq_mul (a := 2) (m := 15) (by rw [hm]; norm_num) (by norm_num)
  have hPi : P.index = 15 := by
    have h : (P : Subgroup G).index * Nat.card P = Nat.card G := P.index_mul_card
    rw [hP, hm] at h
    omega
  let φ : G →* Perm (Sylow 2 G) := toPermHom G (Sylow 2 G)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_card]
    refine (hsimple _ φ.normal_ker).resolve_right fun h ↦ ?_
    have htop : φ.ker = ⊤ := Subgroup.eq_top_of_card_eq _ (h.trans hm.symm)
    have : Subsingleton (Sylow 2 G) := ⟨fun Q Q' ↦ by
      rcases exists_smul_eq G P Q with ⟨g, rfl⟩
      rcases exists_smul_eq G P Q' with ⟨g', rfl⟩
      have hg : g • P = P := DFunLike.congr_fun (htop ▸ Subgroup.mem_top g : g ∈ φ.ker) P
      have hg' : g' • P = P := DFunLike.congr_fun (htop ▸ Subgroup.mem_top g' : g' ∈ φ.ker) P
      rw [hg, hg']⟩
    have hP' : Nat.card P = 1 ∨ Nat.card P = 60 := hsimple P P.normal_of_subsingleton
    omega
  have hn : Nat.card (Sylow 2 G) = 5 := by
    have hmod : Nat.card (Sylow 2 G) ≡ 1 [MOD 2] := card_sylow_modEq_one 2 G
    have hdvd : Nat.card (Sylow 2 G) ∣ 15 := hPi ▸ P.card_dvd_index
    have hle : Nat.card (Sylow 2 G) ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
    have hcard : 60 ≤ (Nat.card (Sylow 2 G)).factorial := by
      rw [← hm, ← Nat.card_perm]
      exact Nat.card_le_card_of_injective φ hφ
    have h15 : Nat.card (Sylow 2 G) ≠ 15 := by
      intro h15
      have hN4 : Nat.card (Subgroup.normalizer (P : Set G)) = 4 := by
        have h : (Subgroup.normalizer (P : Set G)).index *
            Nat.card (Subgroup.normalizer (P : Set G)) = Nat.card G :=
          (Subgroup.normalizer (P : Set G)).index_mul_card
        rw [← P.card_eq_index_normalizer, h15, hm] at h
        omega
      have hN : Subgroup.normalizer (P : Set G) = P :=
        (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (hN4.trans hP.symm).le).symm
      have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hP
      have hle : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
        hN ▸ Subgroup.le_centralizer (P : Subgroup G)
      have hc : Nat.card (MonoidHom.transferSylow P hle).ker * Nat.card P = Nat.card G :=
        (MonoidHom.ker_transferSylow_isComplement' P hle).card_mul_card
      rw [hP, hm] at hc
      have hK : Nat.card (MonoidHom.transferSylow P hle).ker = 1 ∨
          Nat.card (MonoidHom.transferSylow P hle).ker = 60 :=
        hsimple _ (MonoidHom.transferSylow P hle).normal_ker
      omega
    have h4 : 4 ≤ Nat.card (Sylow 2 G) := by
      by_contra! h4
      have h6 : (Nat.card (Sylow 2 G)).factorial ≤ (3 : ℕ).factorial :=
        Nat.factorial_le (Nat.le_of_lt_succ h4)
      rw [(by decide : (3 : ℕ).factorial = 6)] at h6
      omega
    rw [Nat.ModEq] at hmod
    interval_cases h : Nat.card (Sylow 2 G) <;> omega
  have hidx : φ.range.index = 2 := by
    have h : φ.range.index * Nat.card φ.range = Nat.card (Perm (Sylow 2 G)) :=
      φ.range.index_mul_card
    rw [Nat.card_perm, hn, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, hm] at h
    norm_num [Nat.factorial] at h
    omega
  let _ : Fintype (Sylow 2 G) := Fintype.ofFinite _
  exact ⟨(MonoidHom.ofInjective hφ).trans <| (MulEquiv.subgroupCongr
    (Perm.eq_alternatingGroup_of_index_eq_two hidx)).trans
      (altCongrHom (Finite.equivFinOfCardEq hn))⟩

lemma HasTwoFixedPoints.nonempty_mulEquiv_of_le (hG : HasTwoFixedPoints G X) (hx₁ : x₁ ∈ poles G X)
    (hcov : ∀ y ∈ poles G X, y ∈ orbit G x₁ ∨ y ∈ orbit G x₂ ∨ y ∈ orbit G x₃)
    (hsum : (orbit G x₁).ncard + (orbit G x₂).ncard + (orbit G x₃).ncard = Nat.card G + 2)
    (h₁₂ : Nat.card (stabilizer G x₁) ≤ Nat.card (stabilizer G x₂))
    (h₂₃ : Nat.card (stabilizer G x₂) ≤ Nat.card (stabilizer G x₃)) :
    (∃ n, 2 ≤ n ∧ Nonempty (G ≃* DihedralGroup n)) ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Perm (Fin 4)) ∨ Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have ho₁ : (orbit G x₁).ncard * Nat.card (stabilizer G x₁) = Nat.card G :=
    ncard_orbit_mul_card_stabilizer x₁
  have ho₂ : (orbit G x₂).ncard * Nat.card (stabilizer G x₂) = Nat.card G :=
    ncard_orbit_mul_card_stabilizer x₂
  have ho₃ : (orbit G x₃).ncard * Nat.card (stabilizer G x₃) = Nat.card G :=
    ncard_orbit_mul_card_stabilizer x₃
  have hstab : ∀ y ∈ poles G X, Nat.card (stabilizer G y) = Nat.card (stabilizer G x₁) ∨
      Nat.card (stabilizer G y) = Nat.card (stabilizer G x₂) ∨
        Nat.card (stabilizer G y) = Nat.card (stabilizer G x₃) := fun y hy ↦ by
    rcases hcov y hy with h | h | h
    exacts [Or.inl (card_stabilizer_eq_of_mem_orbit h),
      Or.inr (Or.inl (card_stabilizer_eq_of_mem_orbit h)),
      Or.inr (Or.inr (card_stabilizer_eq_of_mem_orbit h))]
  rcases orbit_data (ho₁.trans ho₃.symm) (ho₂.trans ho₃.symm) (two_le_card_stabilizer hx₁) h₁₂ h₂₃
    (by rwa [ho₃]) with ⟨hn₁, hn₂⟩ | ⟨hn₁, hn₂, ⟨hn₃, ho⟩ | ⟨hn₃, ho⟩ | ⟨hn₃, ho⟩⟩
  · have : IsCyclic (stabilizer G x₃) := hG.isCyclic_stabilizer x₃
    have hidx : (stabilizer G x₃).index = 2 := by
      rw [index_stabilizer]
      rw [hn₁] at ho₁
      rw [hn₂] at ho₂
      omega
    exact Or.inl ⟨_, hn₁ ▸ h₁₂.trans h₂₃, DihedralGroup.nonempty_mulEquiv_of_index_eq_two hidx
      fun g hg ↦ hG.pow_two_eq_one hcov hn₁ hn₂ hidx hg⟩
  · exact Or.inr <| Or.inl <| hG.nonempty_mulEquiv_alternatingGroup_four (by rw [← ho₃, ho, hn₃]) ho
  · exact Or.inr <| Or.inr <| Or.inl <| hG.nonempty_mulEquiv_perm_four (by rw [← ho₃, ho, hn₃])
      fun y hy ↦ by rcases hstab y hy with h | h | h <;> omega
  · exact Or.inr <| Or.inr <| Or.inr <| hG.nonempty_mulEquiv_alternatingGroup_five
      (by rw [← ho₃, ho, hn₃]) fun y hy ↦ by rcases hstab y hy with h | h | h <;> omega

/-- **Classification of the finite groups acting with two fixed points**: such a group is cyclic,
dihedral of order `2n` with `n ≥ 2`, or isomorphic to `A₄`, `S₄` or `A₅`. A group that fixes a
point is the stabiliser of that point, which is cyclic; otherwise there are three orbits of poles,
with stabilisers of orders `(2, 2, n)`, `(2, 3, 3)`, `(2, 3, 4)` or `(2, 3, 5)`. -/
lemma HasTwoFixedPoints.classification (hG : HasTwoFixedPoints G X) : IsCyclic G ∨
    (∃ n, 2 ≤ n ∧ Nonempty (G ≃* DihedralGroup n)) ∨ Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Perm (Fin 4)) ∨ Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  by_cases hX : ∃ x : X, stabilizer G x = ⊤
  · rcases hX with ⟨x, hx⟩
    have : IsCyclic (stabilizer G x) := hG.isCyclic_stabilizer x
    exact Or.inl <| isCyclic_of_surjective (stabilizer G x).subtype fun g ↦
      ⟨⟨g, hx ▸ Subgroup.mem_top g⟩, rfl⟩
  push Not at hX
  rcases subsingleton_or_nontrivial G with hG1 | hG1
  · exact Or.inl inferInstance
  rcases hG.exists_three_orbits hX with ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, hcov, hsum⟩
  refine Or.inr ?_
  rcases le_total (Nat.card (stabilizer G x₁)) (Nat.card (stabilizer G x₂)) with h₁₂ | h₁₂ <;>
    rcases le_total (Nat.card (stabilizer G x₂)) (Nat.card (stabilizer G x₃)) with h₂₃ | h₂₃ <;>
    rcases le_total (Nat.card (stabilizer G x₁)) (Nat.card (stabilizer G x₃)) with h₁₃ | h₁₃ <;>
    first
    | exact hG.nonempty_mulEquiv_of_le hx₁ hcov hsum (by omega) (by omega)
    | exact hG.nonempty_mulEquiv_of_le (x₁ := x₁) (x₂ := x₃) (x₃ := x₂) hx₁
        (fun y hy ↦ by rcases hcov y hy with h | h | h <;> simp [h]) (by omega) (by omega)
        (by omega)
    | exact hG.nonempty_mulEquiv_of_le (x₁ := x₂) (x₂ := x₁) (x₃ := x₃) hx₂
        (fun y hy ↦ by rcases hcov y hy with h | h | h <;> simp [h]) (by omega) (by omega)
        (by omega)
    | exact hG.nonempty_mulEquiv_of_le (x₁ := x₂) (x₂ := x₃) (x₃ := x₁) hx₂
        (fun y hy ↦ by rcases hcov y hy with h | h | h <;> simp [h]) (by omega) (by omega)
        (by omega)
    | exact hG.nonempty_mulEquiv_of_le (x₁ := x₃) (x₂ := x₁) (x₃ := x₂) hx₃
        (fun y hy ↦ by rcases hcov y hy with h | h | h <;> simp [h]) (by omega) (by omega)
        (by omega)
    | exact hG.nonempty_mulEquiv_of_le (x₁ := x₃) (x₂ := x₂) (x₃ := x₁) hx₃
        (fun y hy ↦ by rcases hcov y hy with h | h | h <;> simp [h]) (by omega) (by omega)
        (by omega)

end MulAction
