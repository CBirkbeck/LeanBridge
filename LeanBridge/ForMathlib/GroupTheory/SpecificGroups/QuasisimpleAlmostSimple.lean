import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.AlmostSimple
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Quasisimple
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Parity
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Almost simple groups that are not quasisimple, and conversely

Every non-abelian simple group is both almost simple and quasisimple, but neither property implies
the other (LMFDB `group.quasisimple`, `group.almost_simple`). The symmetric group `S_n` for `n ≥ 5`
lies between the simple group `A_n` and its automorphism group, so it is almost simple, but it is
not perfect, so it is not quasisimple. Conversely `SL(2, F)` is quasisimple when `F` has an element
`a ≠ 0` with `a² ≠ 1`, but an almost simple group has trivial centre while `-1` is central in
`SL(2, F)`, so `SL(2, F)` is not almost simple when `-1 ≠ 1` in `F`; for instance
`SL(2, 5) = 2.A_5`.

## Main results

* `IsAlmostSimple.center_eq_bot`: an almost simple group has trivial centre.
* `Equiv.Perm.isAlmostSimple` (LMFDB `group.quasisimple`, `group.almost_simple`): `S_n` is almost
  simple for `n ≥ 5`.
* `Equiv.Perm.not_isQuasisimple` (LMFDB `group.quasisimple`): `S_n` is not quasisimple for
  `n ≥ 2`.
* `Equiv.Perm.isAlmostSimple_fin_five`, `Equiv.Perm.not_isQuasisimple_fin_five` (LMFDB
  `group.quasisimple`): `S_5` is almost simple and not quasisimple.
* `Matrix.SpecialLinearGroup.isQuasisimple_two` (LMFDB `group.quasisimple`): `SL(2, F)` is
  quasisimple when some `a ≠ 0` in `F` has `a² ≠ 1`.
* `Matrix.SpecialLinearGroup.not_isAlmostSimple_two` (LMFDB `group.quasisimple`): `SL(2, F)` is not
  almost simple when `-1 ≠ 1` in `F`.
* `Matrix.SpecialLinearGroup.isQuasisimple_two_zmod_five`,
  `Matrix.SpecialLinearGroup.not_isAlmostSimple_two_zmod_five` (LMFDB `group.quasisimple`):
  `SL(2, 5)` is quasisimple and not almost simple.
-/

open Equiv Perm Subgroup

open scoped MatrixGroups

variable {G : Type*} [Group G]

/-- **An almost simple group has trivial centre**: a central element acts on the simple group `S`
by an automorphism commuting with all inner automorphisms, hence trivially, as `S` has trivial
centre. -/
lemma IsAlmostSimple.center_eq_bot (h : IsAlmostSimple G) : center G = ⊥ := by
  rcases h with ⟨S, _, hS, hSc, f, hf, hle⟩
  have hn : (center S).Normal := inferInstance
  have hcS : center S = ⊥ := hn.eq_bot_or_eq_top.resolve_right fun h ↦
    hSc (center_eq_top_iff.mp h)
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot, ← map_eq_one_iff f hf]
  refine MulEquiv.ext fun t ↦ ?_
  rcases hle ⟨t, rfl⟩ with ⟨g, hg⟩
  have hcomm : f z * f g = f g * f z := by rw [← map_mul, ← map_mul, mem_center_iff.mp hz g]
  have key (u : S) : f z t * u * (f z t)⁻¹ = t * u * t⁻¹ := by
    simpa [hg] using congrArg (fun ψ : MulAut S ↦ ψ ((f z).symm u)) hcomm
  have hmem : t⁻¹ * f z t ∈ center S := mem_center_iff.mpr fun u ↦ by
    rw [mul_assoc, mul_inv_eq_iff_eq_mul.mp (key u)]
    simp [mul_assoc]
  rw [hcS, mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

lemma eq_one_of_forall_commute_alternatingGroup (h4 : 4 ≤ Nat.card α) {g : Perm α}
    (hg : ∀ k ∈ alternatingGroup α, g * k = k * g) : g = 1 := by
  refine Equiv.ext fun a ↦ ?_
  by_contra hab
  rw [one_apply] at hab
  have hcard : 2 ≤ (({a, g a} : Finset α)ᶜ).card := by
    rw [← Nat.add_le_add_iff_left, Finset.card_add_card_compl, ← Nat.card_eq_fintype_card,
      Finset.card_pair (Ne.symm hab)]
    exact h4
  rw [← Nat.lt_iff_add_one_le, Finset.one_lt_card_iff] at hcard
  rcases hcard with ⟨c, d, hc, hd, hcd⟩
  simp only [Finset.compl_insert, Finset.mem_erase, Finset.mem_compl, Finset.mem_singleton,
    ← ne_eq] at hc hd
  have hk : swap (g a) d * swap (g a) c ∈ alternatingGroup α := by
    simp [hc.2.symm, hd.2.symm]
  have h : g (swap (g a) d (swap (g a) c a)) = swap (g a) d (swap (g a) c (g a)) :=
    congrArg (· a) (hg _ hk)
  rw [swap_apply_of_ne_of_ne (Ne.symm hab) hc.1.symm, swap_apply_of_ne_of_ne (Ne.symm hab)
    hd.1.symm, swap_apply_left, swap_apply_of_ne_of_ne hc.2 hcd] at h
  exact hc.2 h.symm

/-- **The symmetric group `S_n` is almost simple for `n ≥ 5`** (LMFDB `group.quasisimple`,
`group.almost_simple`): it acts faithfully by conjugation on the non-abelian simple group `A_n`, by
automorphisms that include all inner automorphisms of `A_n`. -/
lemma isAlmostSimple (h5 : 5 ≤ Nat.card α) : IsAlmostSimple (Perm α) := by
  refine ⟨alternatingGroup α, inferInstance, alternatingGroup.isSimpleGroup h5, ?_,
    MulAut.conjNormal, (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_, ?_⟩
  · rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    omega
  · refine eq_one_of_forall_commute_alternatingGroup (by omega) fun k hk ↦ ?_
    have h : g * k * g⁻¹ = k :=
      congrArg (fun φ : MulAut (alternatingGroup α) ↦ (φ ⟨k, hk⟩ : Perm α)) hg
    exact mul_inv_eq_iff_eq_mul.mp h
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, MulEquiv.ext fun t ↦ Subtype.ext (by simp)⟩

/-- **The symmetric group `S_n` is not quasisimple for `n ≥ 2`** (LMFDB `group.quasisimple`): it
is not perfect, its commutator subgroup lying in the alternating group. -/
lemma not_isQuasisimple (h2 : 2 ≤ Nat.card α) : ¬IsQuasisimple (Perm α) := fun h ↦ by
  rcases (Finite.one_lt_card_iff_nontrivial.mp h2).exists_pair_ne with ⟨a, b, hab⟩
  have hmem : swap a b ∈ alternatingGroup α :=
    alternatingGroup.commutator_perm_le (h.isPerfect.commutator_eq_top ▸ mem_top (swap a b))
  rw [mem_alternatingGroup, sign_swap hab] at hmem
  exact absurd hmem (by decide)

end Equiv.Perm

namespace Matrix.SpecialLinearGroup

variable {F : Type*} [Field F]

/-- **`SL(2, F)` is quasisimple** (LMFDB `group.quasisimple`) when `F` has an element `a ≠ 0` with
`a² ≠ 1`, as when `|F| ≥ 4`: it is perfect and `SL(2, F) ⧸ Z = PSL(2, F)` is simple. -/
lemma isQuasisimple_two {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) : IsQuasisimple SL(2, F) :=
  isQuasisimple_iff_isSimpleGroup_quotient_center.mpr
    ⟨⟨SL2.commutator_eq_top ha hasq⟩, ProjectiveSpecialLinearGroup.rank_two_simple' ⟨a, ha, hasq⟩⟩

/-- **`SL(2, F)` is not almost simple when `-1 ≠ 1` in `F`** (LMFDB `group.quasisimple`): `-1` is
a nontrivial central element, while almost simple groups have trivial centre. -/
lemma not_isAlmostSimple_two (h : (-1 : F) ≠ 1) : ¬IsAlmostSimple SL(2, F) := fun hF ↦ by
  have hmem : (-1 : SL(2, F)) ∈ center SL(2, F) :=
    Subgroup.mem_center_iff.mpr fun B ↦ by rw [mul_neg_one, neg_one_mul]
  rw [hF.center_eq_bot, mem_bot] at hmem
  exact h (by simpa using congrArg (fun A : SL(2, F) ↦ (A : Matrix (Fin 2) (Fin 2) F) 0 0) hmem)

/-- **`SL(2, 5)` is quasisimple** (LMFDB `group.quasisimple`). -/
lemma isQuasisimple_two_zmod_five : IsQuasisimple SL(2, ZMod 5) := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have h4 : (2 : ZMod 5) ^ 2 ≠ 1 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact isQuasisimple_two h2 h4

/-- **`SL(2, 5)` is not almost simple** (LMFDB `group.quasisimple`): quasisimple groups need not
be almost simple. -/
lemma not_isAlmostSimple_two_zmod_five : ¬IsAlmostSimple SL(2, ZMod 5) := by
  have h : (-1 : ZMod 5) ≠ 1 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact not_isAlmostSimple_two h

end Matrix.SpecialLinearGroup

namespace Equiv.Perm

/-- **`S_5` is almost simple** (LMFDB `group.quasisimple`). -/
lemma isAlmostSimple_fin_five : IsAlmostSimple (Perm (Fin 5)) :=
  isAlmostSimple (by simp)

/-- **`S_5` is not quasisimple** (LMFDB `group.quasisimple`): almost simple groups need not be
quasisimple. -/
lemma not_isQuasisimple_fin_five : ¬IsQuasisimple (Perm (Fin 5)) :=
  not_isQuasisimple (by simp)

end Equiv.Perm
