import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.CyclicIndexTwoClassification

/-!
# The other-dihedral group among the semidirect products `C_{2^{k-1}} ⋊ C_2`

The LMFDB describes the other-dihedral group `OD_n`, `n = 2 ^ k`, as "the non-trivial semidirect
product `C_{2^{k-1}} : C_2` which is not isomorphic to either `SD_n` or `D_{2^{k-1}}`" (LMFDB
`group.name`, `group.other_dihedral`). For `k ≥ 4` this description is right. A semidirect product
`N ⋊[φ] H` of a cyclic group `N` of order `2 ^ (k - 1)` by a group `H` of order `2`, with a
non-trivial action `φ`, is a non-abelian group of order `2 ^ k` with a cyclic subgroup of index
`2`, the image of `N`. So it is isomorphic to `D_{2^{k-1}}`, `Q_{2^k}`, `SD_{2^k}` or `OD_{2^k}`
(`nonempty_mulEquiv_of_isCyclic_of_index_eq_two`), and it is not `Q_{2^k}`, in which `g² = 1` has
two solutions, since `1`, an involution of `N` and the generator of `H` are three. Conversely
`OD_{2^k}` is such a semidirect product, isomorphic to neither `SD_{2^k}` nor `D_{2^{k-1}}`. For
`k = 3` the description fails: `C_4` has a single non-trivial automorphism, so the only non-trivial
semidirect product `C_4 ⋊ C_2` is `D_4`, which is `OD_8`.

## Main results

* `ZMod.involutionMulAut_otherDihedralUnit_ne_one`: the action of `C_2` on `C_{2^{k-1}}` that
  defines `OD_{2^k}` is non-trivial.
* `OtherDihedralGroup.nonempty_mulEquiv_dihedralGroup`: `OD_8` is the dihedral group `D_4`.
* `SemidirectProduct.nonempty_mulEquiv_otherDihedralGroup_iff`: for `k ≥ 4`, a non-trivial
  semidirect product `C_{2^{k-1}} ⋊ C_2` is isomorphic to `OD_{2^k}` if and only if it is
  isomorphic to neither `SD_{2^k}` nor `D_{2^{k-1}}`.
-/

open Multiplicative Subgroup ZMod

variable {k : ℕ} [Fact (3 ≤ k)]

/-- **The action of `C_2` on `C_{2^{k-1}}` that defines `OD_{2^k}` is non-trivial** (LMFDB
`group.name`): the generator of `C_2` acts by `x ↦ x ^ (2 ^ (k - 2) + 1)`, which is not the
identity. -/
lemma ZMod.involutionMulAut_otherDihedralUnit_ne_one :
    involutionMulAut _ (otherDihedralUnit_pow_two k) ≠ 1 :=
  unitPowMulAut_ne_one _ _ (OtherDihedralGroup.val_otherDihedralUnit_ne_one k)

variable [Fact (3 ≤ 3)] in
/-- **`OD_8` is the dihedral group `D_4`** (LMFDB `group.name`, `group.other_dihedral`): for
`k = 3` the generator of `C_2` acts on `C_4` by `x ↦ x ^ 3 = x⁻¹`. So the LMFDB's description of
`OD_{2^k}`, as a semidirect product isomorphic to neither `SD_{2^k}` nor `D_{2^{k-1}}`, needs
`k ≥ 4`. -/
lemma OtherDihedralGroup.nonempty_mulEquiv_dihedralGroup :
    Nonempty (OtherDihedralGroup 3 ≃* DihedralGroup 4) := by
  have key (u : (ZMod (2 ^ (3 - 1)))ˣ) (hu : u ^ 2 = 1) (h : u = -1) :
      Nonempty (Multiplicative (ZMod (2 ^ (3 - 1))) ⋊[involutionMulAut u hu]
        Multiplicative (ZMod 2) ≃* DihedralGroup 4) := by
    subst h
    exact ⟨(DihedralGroup.mulEquivSemidirectProduct 4).symm⟩
  exact key _ _ <| Units.ext (by decide : (2 ^ (3 - 2) + 1 : ZMod (2 ^ (3 - 1))) = -1)

namespace SemidirectProduct

variable {N H : Type*} [Group N] [Group H] {φ : H →* MulAut N}

private lemma three_le_card_sq_eq_one [Finite N] [Finite H] {n₀ : N} {h₀ : H} (hn₀ : n₀ ≠ 1)
    (hn₀2 : n₀ ^ 2 = 1) (hh₀ : h₀ ≠ 1) (hh₀2 : h₀ ^ 2 = 1) :
    3 ≤ Nat.card {g : N ⋊[φ] H // g ^ 2 = 1} := by
  have : Finite (N ⋊[φ] H) := Finite.of_equiv _ equivProd.symm
  have hS : ({1, inl n₀, inr h₀} : Set (N ⋊[φ] H)) ⊆ {g | g ^ 2 = 1} := by
    rintro g (rfl | rfl | rfl)
    · exact one_pow 2
    · rw [Set.mem_ofPred_eq, ← map_pow, hn₀2, map_one]
    · rw [Set.mem_ofPred_eq, ← map_pow, hh₀2, map_one]
  have h3 : ({1, inl n₀, inr h₀} : Set (N ⋊[φ] H)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, inl n₀, inr h₀, fun h ↦ hn₀ (inl_injective (h.symm.trans
      (map_one inl).symm)), fun h ↦ hh₀ (inr_injective (h.symm.trans (map_one inr).symm)),
      fun h ↦ hh₀ (congrArg right h).symm, rfl⟩
  exact h3 ▸ Set.ncard_le_ncard hS (Set.toFinite _)

/-- **`OD_{2^k}` is the non-trivial semidirect product `C_{2^{k-1}} ⋊ C_2` which is isomorphic to
neither `SD_{2^k}` nor `D_{2^{k-1}}`** (LMFDB `group.name`, `group.other_dihedral`), for `k ≥ 4`:
a semidirect product `N ⋊[φ] H` of a cyclic group `N` of order `2 ^ (k - 1)` by a group `H` of
order `2`, with `φ` non-trivial, is isomorphic to `OD_{2^k}` if and only if it is isomorphic to
neither `SD_{2^k}` nor `D_{2^{k-1}}`. -/
lemma nonempty_mulEquiv_otherDihedralGroup_iff (hk : 4 ≤ k) [IsCyclic N]
    (hN : Nat.card N = 2 ^ (k - 1)) (hH : Nat.card H = 2) (hφ : φ ≠ 1) :
    Nonempty (N ⋊[φ] H ≃* OtherDihedralGroup k) ↔ IsEmpty (N ⋊[φ] H ≃* SemiDihedralGroup k) ∧
      IsEmpty (N ⋊[φ] H ≃* DihedralGroup (2 ^ (k - 1))) := by
  refine ⟨fun ⟨e⟩ ↦ ⟨⟨fun f ↦ (SemiDihedralGroup.isEmpty_mulEquiv_otherDihedralGroup hk).false
    (f.symm.trans e)⟩, ⟨fun f ↦ (DihedralGroup.isEmpty_mulEquiv_otherDihedralGroup hk).false
    (f.symm.trans e)⟩⟩, fun ⟨hSD, hD⟩ ↦ ?_⟩
  have : Finite N := Nat.finite_of_card_ne_zero (hN ▸ (pow_pos two_pos _).ne')
  have : Finite H := Nat.finite_of_card_ne_zero (hH ▸ two_ne_zero)
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hcard : Nat.card (N ⋊[φ] H) = 2 ^ k := by
    rw [card, hN, hH, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have : IsCyclic (inl : N →* N ⋊[φ] H).range := isCyclic_range_inl
  rcases nonempty_mulEquiv_of_isCyclic_of_index_eq_two hk hcard (index_range_inl_eq.trans hH)
    (not_isMulCommutative_of_ne_one hφ) with hD' | hQ | hSD' | hOD
  · exact (hD.false hD'.some).elim
  · rcases exists_prime_orderOf_dvd_card' 2 (hN ▸ dvd_pow_self 2 (by omega)) with ⟨n₀, hn₀⟩
    have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; norm_num)
    rcases exists_ne (1 : H) with ⟨h₀, hh₀⟩
    have h3 : 3 ≤ Nat.card {g : N ⋊[φ] H // g ^ 2 = 1} :=
      three_le_card_sq_eq_one (fun h ↦ by simp [h] at hn₀) (hn₀ ▸ pow_orderOf_eq_one n₀) hh₀
        (hH ▸ pow_card_eq_one')
    rw [hQ.some.card_sq_eq_one, QuaternionGroup.card_sq_eq_one] at h3
    omega
  · exact (hSD.false hSD'.some).elim
  · exact hOD

end SemidirectProduct
