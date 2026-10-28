import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# The primary decomposition of a finite abelian group

Every finite abelian group is isomorphic to a finite product of cyclic groups of prime-power order
(Mathlib's `AddCommGroup.equiv_directSum_zmod_of_finite`), and the orders of the factors are unique
up to reordering. We prove the uniqueness by counting torsion: the `n`-torsion subgroup of
`Π i, ZMod (q i)` has `∏ i, gcd (q i) n` elements, and when every `q i` is a prime power these
numbers, for `n` running over the powers of a prime `p`, determine how many of the `q i` are equal
to each power of `p`. The same count shows that two finite abelian groups are isomorphic as soon as
their `n`-torsion subgroups have the same number of elements for every `n`.

The statements are about additive groups; those about a multiplicative group `G` are obtained
through `Additive G`.

## Main results

* `AddCommGroup.exists_addEquiv_pi_zmod_isPrimePow` (LMFDB `group.primary_decomposition`): a finite
  abelian group is a finite product of cyclic groups of prime-power order.
* `AddCommGroup.exists_equiv_of_addEquiv_pi_zmod` (LMFDB `group.primary_decomposition`): the
  orders of the factors are unique up to reordering.
* `AddCommGroup.nonempty_addEquiv_of_card_ker_nsmul_eq`: two finite abelian groups whose
  `n`-torsion subgroups have the same number of elements for every `n` are isomorphic.
-/

open Finset

namespace AddCommGroup

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {q : ι → ℕ} {q' : κ → ℕ} {G H : Type*}
  [AddCommGroup G] [AddCommGroup H] (n : ℕ) (hq : ∀ i, IsPrimePow (q i))
  (hq' : ∀ j, IsPrimePow (q' j)) (hgcd : ∀ n, ∏ i, (q i).gcd n = ∏ j, (q' j).gcd n)
  (e : G ≃+ Π i, ZMod (q i))

variable (q) in
lemma card_ker_nsmul_pi_zmod [∀ i, NeZero (q i)] :
    Nat.card (nsmulAddMonoidHom n : (Π i, ZMod (q i)) →+ Π i, ZMod (q i)).ker =
      ∏ i, (q i).gcd n := by
  rw [Nat.card_congr <| (Equiv.subtypeEquivRight fun x ↦ by simp [funext_iff]).trans
    (Equiv.subtypePiEquivPi (p := fun i (y : ZMod (q i)) ↦ n • y = 0)), Nat.card_pi]
  refine prod_congr rfl fun i _ ↦
    (IsAddCyclic.card_nsmulAddMonoidHom_ker (G := ZMod (q i)) n).trans ?_
  rw [Nat.card_zmod]

lemma card_ker_nsmul_congr (f : G ≃+ H) :
    Nat.card (nsmulAddMonoidHom n : G →+ G).ker = Nat.card (nsmulAddMonoidHom n : H →+ H).ker :=
  Nat.card_congr <| f.toEquiv.subtypeEquiv fun x ↦ by simp [← map_nsmul]

include hq in
private lemma sum_min_add_card_eq {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ∑ i, min ((q i).factorization p) (k + 1) + ∑ i, min ((q i).factorization p) (k - 1) +
      Fintype.card {i // q i = p ^ k} = 2 * ∑ i, min ((q i).factorization p) k := by
  classical
  rw [Fintype.card_subtype, card_filter, ← sum_add_distrib, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rcases (isPrimePow_nat_iff _).mp (hq i) with ⟨ℓ, r, hℓ, hr, hqi⟩
  rw [← hqi, hℓ.factorization_pow, Finsupp.single_apply]
  by_cases hℓp : ℓ = p
  · subst hℓp
    simp only [(Nat.pow_right_injective hℓ.two_le).eq_iff]
    split_ifs <;> omega
  · have hne : ℓ ^ r ≠ p ^ k := fun h ↦ hℓp <| (Nat.prime_dvd_prime_iff_eq hℓ hp).mp <|
      hℓ.dvd_of_dvd_pow <| h ▸ dvd_pow_self ℓ hr.ne'
    simp [hℓp, hne]

include hq hq' hgcd in
lemma card_fiber_eq_of_prod_gcd_eq (a : ℕ) :
    Fintype.card {i // q i = a} = Fintype.card {j // q' j = a} := by
  by_cases ha : IsPrimePow a
  · rcases (isPrimePow_nat_iff a).mp ha with ⟨p, k, hp, hk, rfl⟩
    have hS (m : ℕ) : ∑ i, min ((q i).factorization p) m = ∑ j, min ((q' j).factorization p) m := by
      simpa [Nat.factorization_prod, Nat.factorization_gcd, (hq _).ne_zero, (hq' _).ne_zero,
        hp.ne_zero, hp.factorization_pow] using congrArg (·.factorization p) (hgcd (p ^ m))
    linarith [sum_min_add_card_eq hq hp hk.ne', sum_min_add_card_eq hq' hp hk.ne', hS (k + 1),
      hS (k - 1), hS k]
  · have : IsEmpty {i // q i = a} := ⟨fun i ↦ ha (i.2 ▸ hq i)⟩
    have : IsEmpty {j // q' j = a} := ⟨fun j ↦ ha (j.2 ▸ hq' j)⟩
    simp only [Fintype.card_of_isEmpty]

include hq hq' hgcd in
lemma exists_equiv_of_prod_gcd_eq : ∃ σ : ι ≃ κ, ∀ i, q' (σ i) = q i :=
  ⟨Equiv.ofFiberEquiv fun a ↦ Fintype.equivOfCardEq <| card_fiber_eq_of_prod_gcd_eq hq hq' hgcd a,
    Equiv.ofFiberEquiv_map _⟩

include e in
lemma prod_gcd_eq_card_ker_nsmul (hq₀ : ∀ i, q i ≠ 0) :
    ∏ i, (q i).gcd n = Nat.card (nsmulAddMonoidHom n : G →+ G).ker := by
  have (i : ι) : NeZero (q i) := ⟨hq₀ i⟩
  rw [card_ker_nsmul_congr n e, card_ker_nsmul_pi_zmod]

include hq hq' e in
/-- **Uniqueness of the primary decomposition**: two decompositions of an abelian group as finite
products of cyclic groups of prime-power order have the same factors up to reordering. -/
lemma exists_equiv_of_addEquiv_pi_zmod (e' : G ≃+ Π j, ZMod (q' j)) :
    ∃ σ : ι ≃ κ, ∀ i, q' (σ i) = q i :=
  exists_equiv_of_prod_gcd_eq hq hq' fun n ↦
    (prod_gcd_eq_card_ker_nsmul n e (hq · |>.ne_zero)).trans
      (prod_gcd_eq_card_ker_nsmul n e' (hq' · |>.ne_zero)).symm

variable [Finite G] [Finite H]

variable (G) in
/-- **Existence of the primary decomposition**: a finite abelian group is isomorphic to a finite
product of cyclic groups of prime-power order. -/
lemma exists_addEquiv_pi_zmod_isPrimePow : ∃ (ι : Type) (_ : Fintype ι) (q : ι → ℕ),
    (∀ i, IsPrimePow (q i)) ∧ Nonempty (G ≃+ Π i, ZMod (q i)) := by
  classical
  rcases equiv_directSum_zmod_of_finite G with ⟨ι, _, p, hp, r, ⟨f⟩⟩
  have (i : {i // ¬r i ≠ 0}) : Subsingleton (ZMod (p i ^ r i)) :=
    ZMod.subsingleton_iff.mpr <| by rw [not_not.mp i.2, pow_zero]
  let : Unique (Π i : {i // ¬r i ≠ 0}, ZMod (p i ^ r i)) := uniqueOfSubsingleton 0
  exact ⟨{i // r i ≠ 0}, inferInstance, fun i ↦ p i ^ r i, fun i ↦ (hp i).isPrimePow.pow i.2,
    ⟨f.trans <| (DirectSum.addEquivProd _).trans <|
      (RingEquiv.piEquivPiSubtypeProd (fun i ↦ r i ≠ 0) _).toAddEquiv.trans AddEquiv.prodUnique⟩⟩

/-- **A finite abelian group is determined by the orders of its torsion subgroups**: two finite
abelian groups whose `n`-torsion subgroups have the same number of elements for every `n` are
isomorphic. -/
lemma nonempty_addEquiv_of_card_ker_nsmul_eq (h : ∀ n, Nat.card (nsmulAddMonoidHom n : G →+ G).ker =
    Nat.card (nsmulAddMonoidHom n : H →+ H).ker) : Nonempty (G ≃+ H) := by
  rcases exists_addEquiv_pi_zmod_isPrimePow G with ⟨ι, _, q, hq, ⟨e⟩⟩
  rcases exists_addEquiv_pi_zmod_isPrimePow H with ⟨κ, _, q', hq', ⟨e'⟩⟩
  rcases exists_equiv_of_prod_gcd_eq hq hq' fun n ↦
    (prod_gcd_eq_card_ker_nsmul n e (hq · |>.ne_zero)).trans <|
      (h n).trans (prod_gcd_eq_card_ker_nsmul n e' (hq' · |>.ne_zero)).symm with ⟨σ, hσ⟩
  exact ⟨e.trans <| ((RingEquiv.piCongrRight fun i ↦ ZMod.ringEquivCongr (hσ i).symm).trans
    (RingEquiv.piCongrLeft (fun j ↦ ZMod (q' j)) σ)).toAddEquiv.trans e'.symm⟩

end AddCommGroup
