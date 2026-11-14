import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Metacyclic
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.GroupTheory.SpecificGroups.Affine.Basic

/-!
# The Frobenius group `F_q`

The Frobenius group `F_q` (LMFDB `group.frobenius`) is the group of the maps `x ↦ a x + b` of a
finite field `𝔽_q` with `a ≠ 0`, under composition. Tau Ceti's `TauCeti.AffineGroup F` is the
semidirect product `F ⋊ Fˣ`, acting faithfully on `F` by `x ↦ b + a x`
(`TauCeti.AffineGroup.smul_def`), of order `q (q - 1)` (`TauCeti.card_affineGroup`). The
permutations of `F` given by its elements are exactly the knowl's maps, so the action identifies it
with the knowl's group of these maps under composition.

The knowl says that `F_q` is a Z-group, hence metacyclic and solvable. It is solvable for every
`q`, as an extension of the abelian group `Fˣ` by the abelian group of translations. It is a
Z-group, and metacyclic, only for prime `q`. For prime `q` it is an extension of the cyclic group
`Fˣ` of order `q - 1` by the cyclic group of translations of order `q`, of coprime orders. For
`q = p ^ k` with `k ≥ 2` the translations form a group isomorphic to `(𝔽_q, +)`, of exponent `p`,
so not cyclic; it would be cyclic in a Z-group. Since `Fˣ` has an element `a ≠ 1`, every
translation `x ↦ x + (a - 1) c` is a commutator, so a normal subgroup with cyclic quotient
contains the translations, and cannot be cyclic.

## Main definitions

* `TauCeti.AffineGroup.mulEquivRangeToPermHom` (LMFDB `group.frobenius`): the isomorphism of the
  affine group with the group of the maps `x ↦ a x + b`, `a ≠ 0`, of `F`.

## Main results

* `TauCeti.AffineGroup.mem_range_toPermHom_iff` (LMFDB `group.frobenius`): the permutations of `F`
  given by the affine group are the maps `x ↦ a x + b` with `a ≠ 0`.
* `TauCeti.AffineGroup.isSolvable` (LMFDB `group.frobenius`): `F_q` is solvable.
* `TauCeti.AffineGroup.isZGroup_iff` (LMFDB `group.frobenius`): `F_q` is a Z-group if and only if
  `q` is prime.
* `TauCeti.AffineGroup.isMetacyclic_iff` (LMFDB `group.frobenius`): `F_q` is metacyclic if and only
  if `q` is prime.
-/

open MulAction SemidirectProduct

namespace TauCeti.AffineGroup

lemma mem_affineLinearSubgroup_iff_smul_zero {F : Type*} [Ring F] (g : AffineGroup F) :
    g ∈ affineLinearSubgroup F ↔ g • (0 : F) = 0 := by
  rw [mem_affineLinearSubgroup_iff, smul_def, mul_zero, add_zero]

variable {F : Type*} [Field F]

/-- **The affine group of `F` acts by the maps `x ↦ a x + b` with `a ≠ 0`** (LMFDB
`group.frobenius`): a permutation of `F` is given by an element of `TauCeti.AffineGroup F` exactly
when it is such a map. -/
lemma mem_range_toPermHom_iff (σ : Equiv.Perm F) :
    σ ∈ (toPermHom (AffineGroup F) F).range ↔ ∃ a b : F, a ≠ 0 ∧ ∀ x, σ x = a * x + b := by
  refine ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g.right, g.left.toAdd, g.right.ne_zero, fun x ↦ add_comm _ _⟩
  · rintro ⟨a, b, ha, hσ⟩
    exact ⟨⟨Multiplicative.ofAdd b, Units.mk0 a ha⟩, Equiv.ext fun x ↦ (hσ x).symm ▸ add_comm _ _⟩

variable (F) in
/-- The Frobenius group `F_q` as a group of maps (LMFDB `group.frobenius`): the isomorphism of the
affine group of `F` with its image in the permutations of `F`, the action being faithful. By
`TauCeti.AffineGroup.mem_range_toPermHom_iff` the image is the group of the maps `x ↦ a x + b`,
`a ≠ 0`, under composition. -/
noncomputable def mulEquivRangeToPermHom : AffineGroup F ≃* (toPermHom (AffineGroup F) F).range :=
  MonoidHom.ofInjective toPerm_injective

variable (F) in
/-- **The Frobenius group `F_q` is solvable** (LMFDB `group.frobenius`): it is an extension of the
abelian group `Fˣ` by the abelian group of translations. -/
lemma isSolvable : Group.IsSolvable (AffineGroup F) :=
  Group.isSolvable_of_ker_le_range inl rightHom range_inl_eq_ker_rightHom.ge

lemma inl_mem_of_isCyclic_quotient {N : Subgroup (AffineGroup F)} [N.Normal]
    [IsCyclic (AffineGroup F ⧸ N)] {a : Fˣ} (ha : a ≠ 1) (b : Multiplicative F) : inl b ∈ N := by
  have hc : (a : F) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ ha (Units.ext h)
  let c : Multiplicative F := .ofAdd (((a : F) - 1)⁻¹ * b.toAdd)
  have hb : (inl b : AffineGroup F) = inr a * inl c * (inr a)⁻¹ * (inl c)⁻¹ := by
    rw [← map_inv (inr : Fˣ →* AffineGroup F), ← inl_aut, ← map_inv, ← map_mul]
    congr 1
    refine Multiplicative.toAdd.injective ?_
    simp only [c, toAdd_mul, toAdd_inv, affineAction_apply_toAdd, toAdd_ofAdd]
    field_simp
    ring1
  rw [hb, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    mul_comm' ((inr a : AffineGroup F) : AffineGroup F ⧸ N), mul_inv_cancel_right, mul_inv_cancel]

variable [Finite F]

lemma prime_of_isZGroup_multiplicative [IsZGroup (Multiplicative F)] : (Nat.card F).Prime := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have hdvd : Nat.card F ∣ ringChar F := by
    rw [← Nat.card_congr Multiplicative.toAdd, ← IsZGroup.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g ↦ ?_
    rw [← ofAdd_toAdd g, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero]
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd h Finite.one_lt_card.ne'
  · exact h ▸ hp

lemma isZGroup_of_prime (hF : (Nat.card F).Prime) : IsZGroup (AffineGroup F) := by
  have : Fact (Nat.card F).Prime := ⟨hF⟩
  have : IsCyclic (Multiplicative F) := isCyclic_of_prime_card (Nat.card_congr Multiplicative.toAdd)
  refine isZGroup_of_coprime range_inl_eq_ker_rightHom.ge ?_
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_units]
  exact (Nat.coprime_self_sub_right hF.one_lt.le).mpr (Nat.coprime_one_right _)

/-- **The Frobenius group `F_q` is a Z-group if and only if `q` is prime** (LMFDB
`group.frobenius`). For prime `q` it is an extension of the cyclic group `Fˣ` of order `q - 1` by
the cyclic group of translations of order `q`. Otherwise the translations, isomorphic to
`(𝔽_q, +)` of exponent `p < q`, are not cyclic, while every abelian subgroup of a Z-group is
cyclic. -/
lemma isZGroup_iff : IsZGroup (AffineGroup F) ↔ (Nat.card F).Prime := by
  refine ⟨fun h ↦ ?_, isZGroup_of_prime⟩
  have : IsZGroup (Multiplicative F) :=
    IsZGroup.of_injective (f := (inl : Multiplicative F →* AffineGroup F)) inl_injective
  exact prime_of_isZGroup_multiplicative

/-- **The Frobenius group `F_q` is metacyclic if and only if `q` is prime** (LMFDB
`group.frobenius`). For prime `q` it is a Z-group. Otherwise `q ≥ 4`, and a normal subgroup with
cyclic quotient contains every translation, since the translation by `(a - 1) c` is the commutator
of the multiplication by a unit `a ≠ 1` and the translation by `c`; but the translations do not
form a cyclic group. -/
lemma isMetacyclic_iff : IsMetacyclic (AffineGroup F) ↔ (Nat.card F).Prime := by
  refine ⟨fun ⟨N, hN, hNc, hQc⟩ ↦ ?_, fun hF ↦ ?_⟩
  · by_cases h2 : Nat.card F = 2
    · exact h2 ▸ Nat.prime_two
    have : Nontrivial Fˣ := by
      rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      omega
    rcases exists_ne (1 : Fˣ) with ⟨a, ha⟩
    have : IsCyclic (Multiplicative F) :=
      isCyclic_of_injective ((inl : Multiplicative F →* AffineGroup F).codRestrict N
        (inl_mem_of_isCyclic_quotient ha)) fun x y h ↦ inl_injective (congrArg Subtype.val h)
    exact prime_of_isZGroup_multiplicative
  · have : IsZGroup (AffineGroup F) := isZGroup_of_prime hF
    exact IsZGroup.isMetacyclic

end TauCeti.AffineGroup
