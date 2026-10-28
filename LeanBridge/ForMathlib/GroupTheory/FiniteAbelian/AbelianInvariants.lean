import LeanBridge.ForMathlib.GroupTheory.FiniteAbelian.PrimaryDecomposition

/-!
# Abelian invariants of a finite abelian group

A finite abelian group `A` has two canonical forms as a product `C_{n₁} × ⋯ × C_{nₖ}` of nontrivial
cyclic groups, which the LMFDB records as lists of integers:

* its Smith abelian invariants, or invariant factors: the unique list with `nᵢ ∣ nᵢ₊₁`;
* its primary abelian invariants, or elementary divisors: the unique list of prime powers sorted
  first by the prime and then by size.

The second is the primary decomposition, unique up to reordering by
`AddCommGroup.exists_equiv_of_addEquiv_pi_zmod`, written in a fixed order. For the first, a list of
positive integers is turned into a Smith list by inserting its entries one by one
(`AddCommGroup.insertDvd`), which keeps the orders of the torsion subgroups because
`C_m × C_n ≃ C_{gcd m n} × C_{lcm m n}`; two finite abelian groups with torsion subgroups of the
same orders are isomorphic (`AddCommGroup.nonempty_addEquiv_of_card_ker_nsmul_eq`), and the Smith
list is recovered from these orders: its largest entry is the exponent, the least `n` such that the
`n`-torsion subgroup is the whole group.

The cyclic group `C_n` is `ZMod n`, and the product of the cyclic groups of a list `L` is
`Π i : Fin L.length, ZMod L[i]`. The invariants of a multiplicative group `G` are those of
`Additive G`, which the last two results below characterise in multiplicative terms.

## Main definitions

* `AddCommGroup.insertDvd`: inserts a positive integer into a list of positive integers each
  divisible by the next.
* `AddCommGroup.smithAbelianInvariants` (LMFDB `group.abelian_invariants`).
* `AddCommGroup.primaryAbelianInvariants` (LMFDB `group.abelian_invariants`,
  `group.primary_decomposition`).

## Main results

* `AddCommGroup.exists_isChain_dvd_addEquiv_pi_zmod`: a finite abelian group is a product of
  cyclic groups of orders `n₁ ∣ n₂ ∣ ⋯ ∣ nₖ`, all larger than `1`.
* `AddCommGroup.smithAbelianInvariants_eq_iff`: the Smith abelian invariants are the unique such
  list.
* `AddCommGroup.primaryAbelianInvariants_eq_iff`: the primary abelian invariants are the unique
  list of prime powers, sorted first by the prime and then by size, whose cyclic groups have
  product `A`.
* `CommGroup.smithAbelianInvariants_additive_eq_iff` and
  `CommGroup.primaryAbelianInvariants_additive_eq_iff`: the same characterisations for a
  multiplicative group `G`, whose invariants are those of `Additive G`.
-/

open Finset

namespace AddCommGroup

/-- Inserts a positive integer `a` into a list `l` of positive integers each divisible by the next,
keeping this property and the orders of the torsion subgroups of `Π i, ZMod l[i]`: the head `m` of
`l` becomes `lcm m a` and `gcd m a` is inserted into the tail, since `ZMod m × ZMod a` and
`ZMod (lcm m a) × ZMod (gcd m a)` are isomorphic. A last entry equal to `1` is dropped. -/
def insertDvd (a : ℕ) : List ℕ → List ℕ
  | [] => if a = 1 then [] else [a]
  | m :: l => m.lcm a :: insertDvd (m.gcd a) l

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {a c m n x : ℕ} {l L L' : List ℕ}
  (ha : a ≠ 0) (hl : ∀ m ∈ l, m ≠ 0) (hx : x ∈ insertDvd a l) (hL : ∀ m ∈ L, 1 < m)
  (hL' : ∀ m ∈ L', 1 < m) (e : G ≃+ Π i : Fin L.length, ZMod L[i])

variable (n) in
include ha in
private lemma gcd_lcm_mul_gcd_gcd (hm : m ≠ 0) :
    (m.lcm a).gcd n * (m.gcd a).gcd n = m.gcd n * a.gcd n := by
  have hlcm : m.lcm a ≠ 0 := Nat.lcm_ne_zero hm ha
  have hgcd : m.gcd a ≠ 0 := Nat.gcd_ne_zero_left hm
  refine Nat.eq_of_factorization_eq (mul_ne_zero (Nat.gcd_ne_zero_left hlcm)
    (Nat.gcd_ne_zero_left hgcd)) (mul_ne_zero (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left ha))
    fun p ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.gcd_zero_right, Nat.factorization_mul hlcm hgcd, Nat.factorization_mul hm ha,
      Nat.factorization_lcm hm ha, Nat.factorization_gcd hm ha, Finsupp.add_apply,
      Finsupp.sup_apply, Finsupp.inf_apply]
    omega
  · simp only [Nat.factorization_mul (Nat.gcd_ne_zero_left hlcm) (Nat.gcd_ne_zero_left hgcd),
      Nat.factorization_mul (Nat.gcd_ne_zero_left hm) (Nat.gcd_ne_zero_left ha),
      Nat.factorization_gcd hlcm hn, Nat.factorization_gcd hgcd hn, Nat.factorization_gcd hm hn,
      Nat.factorization_gcd ha hn, Nat.factorization_lcm hm ha, Nat.factorization_gcd hm ha,
      Finsupp.add_apply, Finsupp.sup_apply, Finsupp.inf_apply]
    omega

variable (n) in
include ha hl in
private lemma prod_map_gcd_insertDvd :
    ((insertDvd a l).map (·.gcd n)).prod = a.gcd n * (l.map (·.gcd n)).prod := by
  induction l generalizing a with
  | nil => by_cases h : a = 1 <;> simp [insertDvd, h]
  | cons m l ih =>
    rcases List.forall_mem_cons.mp hl with ⟨hm, hl'⟩
    rw [insertDvd, List.map_cons, List.prod_cons, ih (Nat.gcd_ne_zero_left hm) hl', ← mul_assoc,
      gcd_lcm_mul_gcd_gcd n ha hm, List.map_cons, List.prod_cons]
    ring1

private lemma mem_insertDvd_nil : x ∈ insertDvd a [] ↔ x = a ∧ a ≠ 1 := by
  by_cases h : a = 1 <;> simp [insertDvd, h]

include hx in
private lemma dvd_of_mem_insertDvd (hac : a ∣ c) (hlc : ∀ m ∈ l, m ∣ c) : x ∣ c := by
  induction l generalizing a with
  | nil => exact (mem_insertDvd_nil.mp hx).1 ▸ hac
  | cons m l ih =>
    rcases List.forall_mem_cons.mp hlc with ⟨hmc, hlc'⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.lcm_dvd hmc hac
    · exact ih hx ((Nat.gcd_dvd_right m a).trans hac) hlc'

include ha hx in
private lemma one_lt_of_mem_insertDvd (hl₁ : ∀ m ∈ l, 1 < m) : 1 < x := by
  induction l generalizing a with
  | nil =>
    rcases mem_insertDvd_nil.mp hx with ⟨rfl, h⟩
    omega
  | cons m l ih =>
    rcases List.forall_mem_cons.mp hl₁ with ⟨hm, hl₁'⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hm.trans_le <| Nat.le_of_dvd (Nat.pos_of_ne_zero <| Nat.lcm_ne_zero (by omega) ha) <|
        Nat.dvd_lcm_left m a
    · exact ih (Nat.gcd_ne_zero_left (by omega)) hx hl₁'

private lemma pairwise_insertDvd (hlp : l.Pairwise fun x y ↦ y ∣ x) :
    (insertDvd a l).Pairwise fun x y ↦ y ∣ x := by
  induction l generalizing a with
  | nil => by_cases h : a = 1 <;> simp [insertDvd, h]
  | cons m l ih =>
    rw [List.pairwise_cons] at hlp
    exact List.pairwise_cons.mpr ⟨fun y hy ↦ dvd_of_mem_insertDvd hy
      ((Nat.gcd_dvd_left m a).trans (Nat.dvd_lcm_left m a))
      fun z hz ↦ (hlp.1 z hz).trans (Nat.dvd_lcm_left m a), ih hlp.2⟩

include hl in
private lemma one_lt_of_mem_foldr_insertDvd (hxl : x ∈ l.foldr insertDvd []) : 1 < x := by
  induction l generalizing x with
  | nil => simp at hxl
  | cons a l ih =>
    rcases List.forall_mem_cons.mp hl with ⟨ha, hl'⟩
    exact one_lt_of_mem_insertDvd ha hxl fun _ ↦ ih hl'

variable (n) in
include hl in
private lemma prod_map_gcd_foldr_insertDvd :
    ((l.foldr insertDvd []).map (·.gcd n)).prod = (l.map (·.gcd n)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases List.forall_mem_cons.mp hl with ⟨ha, hl'⟩
    rw [List.foldr_cons, prod_map_gcd_insertDvd n ha
      fun m hm ↦ Nat.ne_zero_of_lt (one_lt_of_mem_foldr_insertDvd hl' hm), ih hl', List.map_cons,
      List.prod_cons]

variable (l) in
private lemma pairwise_foldr_insertDvd : (l.foldr insertDvd []).Pairwise fun x y ↦ y ∣ x := by
  induction l with
  | nil => simp
  | cons a l ih => exact pairwise_insertDvd ih

variable (n) in
include hl in
private lemma prod_map_gcd_le : (l.map (·.gcd n)).prod ≤ l.prod := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rcases List.forall_mem_cons.mp hl with ⟨hm, hl'⟩
    rw [List.map_cons, List.prod_cons, List.prod_cons]
    exact Nat.mul_le_mul (Nat.gcd_le_left n (Nat.pos_of_ne_zero hm)) (ih hl')

include hl in
private lemma prod_map_gcd_eq_prod_iff : (l.map (·.gcd n)).prod = l.prod ↔ ∀ m ∈ l, m ∣ n := by
  induction l with
  | nil => simp
  | cons m l ih =>
    rcases List.forall_mem_cons.mp hl with ⟨hm₀, hl'⟩
    have hm : 0 < m := Nat.pos_of_ne_zero hm₀
    rw [List.map_cons, List.prod_cons, List.prod_cons, List.forall_mem_cons, ← ih hl',
      ← Nat.gcd_eq_left_iff_dvd]
    refine ⟨fun h ↦ ?_, fun ⟨h, h'⟩ ↦ by rw [h, h']⟩
    rcases (Nat.gcd_le_left n hm).lt_or_eq with hlt | heq
    · exact absurd h (Nat.mul_lt_mul_of_lt_of_le hlt (prod_map_gcd_le n hl')
        (List.prod_pos fun x hx ↦ Nat.pos_of_ne_zero (hl' x hx))).ne
    · rw [heq] at h
      exact ⟨heq, Nat.eq_of_mul_eq_mul_left hm h⟩

private lemma prod_map_gcd_eq_prod_iff_dvd (hal : ∀ m ∈ a :: l, 1 < m)
    (hc : (a :: l).Pairwise fun x y ↦ y ∣ x) :
    ((a :: l).map (·.gcd n)).prod = (a :: l).prod ↔ a ∣ n := by
  rw [prod_map_gcd_eq_prod_iff fun m hm ↦ Nat.ne_zero_of_lt (hal m hm), List.forall_mem_cons]
  exact ⟨And.left, fun h ↦ ⟨h, fun m hm ↦ (List.pairwise_cons.mp hc |>.1 m hm).trans h⟩⟩

include hL hL' in
private lemma eq_of_prod_map_gcd_eq (hc : L.Pairwise fun x y ↦ y ∣ x)
    (hc' : L'.Pairwise fun x y ↦ y ∣ x)
    (h : ∀ n, (L.map (·.gcd n)).prod = (L'.map (·.gcd n)).prod) : L = L' := by
  induction L generalizing L' with
  | nil =>
    cases L' with
    | nil => rfl
    | cons b l' =>
      have h₀ : 1 = b * l'.prod := by simpa using h 0
      exact absurd (Nat.eq_one_of_mul_eq_one_right h₀.symm) (hL' b List.mem_cons_self).ne'
  | cons a l ih =>
    cases L' with
    | nil =>
      have h₀ : a * l.prod = 1 := by simpa using h 0
      exact absurd (Nat.eq_one_of_mul_eq_one_right h₀) (hL a List.mem_cons_self).ne'
    | cons b l' =>
      have h₀ : (a :: l).prod = (b :: l').prod := by simpa using h 0
      have hab : a = b := Nat.dvd_antisymm
        ((prod_map_gcd_eq_prod_iff_dvd hL hc).mp <| (h b).trans <|
          ((prod_map_gcd_eq_prod_iff_dvd hL' hc').mpr dvd_rfl).trans h₀.symm)
        ((prod_map_gcd_eq_prod_iff_dvd hL' hc').mp <| (h a).symm.trans <|
          ((prod_map_gcd_eq_prod_iff_dvd hL hc).mpr dvd_rfl).trans h₀)
      subst hab
      rw [List.pairwise_cons] at hc hc'
      congr 1
      refine ih (List.forall_mem_cons.mp hL).2 (List.forall_mem_cons.mp hL').2 hc.2 hc'.2
        fun n ↦ Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left n
          (zero_lt_one.trans (hL a List.mem_cons_self))) ?_
      simpa using h n

include hL in
private lemma neZero_getElem (i : Fin L.length) : NeZero L[i] :=
  ⟨Nat.ne_zero_of_lt (hL _ (List.getElem_mem i.2))⟩

variable (n) in
include hL in
lemma card_ker_nsmul_pi_fin_zmod :
    Nat.card (nsmulAddMonoidHom (α := Π i : Fin L.length, ZMod L[i]) n).ker =
      (L.map (·.gcd n)).prod := by
  have (i : Fin L.length) : NeZero L[i] := neZero_getElem hL i
  rw [card_ker_nsmul_pi_zmod]
  exact Fin.prod_univ_fun_getElem L (·.gcd n)

variable (n) in
include hL e in
lemma prod_map_gcd_eq_card_ker_nsmul :
    (L.map (·.gcd n)).prod = Nat.card (nsmulAddMonoidHom n : G →+ G).ker :=
  (card_ker_nsmul_pi_fin_zmod n hL).symm.trans (card_ker_nsmul_congr n e).symm

include e in
lemma prod_eq_card_of_addEquiv : L.prod = Nat.card G := by
  rw [Nat.card_congr e.toEquiv, Nat.card_pi]
  simp

private lemma map_univ_val_getElem : univ.val.map (fun i : Fin L.length ↦ L[i]) = L := by
  simp only [Fin.univ_val_map, Fin.getElem_fin, List.ofFn_getElem]

variable [Finite G] [Finite H]

include hL in
lemma nonempty_addEquiv_pi_fin_zmod (h : ∀ n, Nat.card (nsmulAddMonoidHom n : G →+ G).ker =
    (L.map (·.gcd n)).prod) : Nonempty (G ≃+ Π i : Fin L.length, ZMod L[i]) := by
  have (i : Fin L.length) : NeZero L[i] := neZero_getElem hL i
  exact nonempty_addEquiv_of_card_ker_nsmul_eq fun n ↦
    (h n).trans (card_ker_nsmul_pi_fin_zmod n hL).symm

variable (G) in
/-- **Invariant factor decomposition**: a finite abelian group is a product of cyclic groups of
orders `n₁ ∣ n₂ ∣ ⋯ ∣ nₖ`, all larger than `1`. -/
lemma exists_isChain_dvd_addEquiv_pi_zmod : ∃ L : List ℕ, (∀ m ∈ L, 1 < m) ∧ L.IsChain (· ∣ ·) ∧
    Nonempty (G ≃+ Π i : Fin L.length, ZMod L[i]) := by
  classical
  rcases equiv_directSum_zmod_of_finite' G with ⟨ι, _, q, hq, ⟨e⟩⟩
  have hl : ∀ a ∈ univ.toList.map q, a ≠ 0 := by
    simpa using fun i ↦ Nat.ne_zero_of_lt (hq i)
  have hL (m : ℕ) (hm : m ∈ ((univ.toList.map q).foldr insertDvd []).reverse) : 1 < m :=
    one_lt_of_mem_foldr_insertDvd hl (List.mem_reverse.mp hm)
  refine ⟨_, hL, List.isChain_iff_pairwise.mpr <| List.pairwise_reverse.mpr <|
    pairwise_foldr_insertDvd _, nonempty_addEquiv_pi_fin_zmod hL fun k ↦ ?_⟩
  rw [← prod_gcd_eq_card_ker_nsmul k (e.trans (DirectSum.addEquivProd _))
    fun i ↦ Nat.ne_zero_of_lt (hq i), List.map_reverse, List.prod_reverse,
    prod_map_gcd_foldr_insertDvd k hl, List.map_map, prod_map_toList]
  rfl

variable (G) in
/-- The **Smith abelian invariants** of a finite abelian group `A` (LMFDB
`group.abelian_invariants`), or its invariant factors: the unique list `[m₁, …, mₖ]` of integers
larger than `1` such that `mᵢ ∣ mᵢ₊₁` for all `i` and `A ≃ C_{m₁} × ⋯ × C_{mₖ}`
(`AddCommGroup.smithAbelianInvariants_eq_iff`). Here `C_m` is `ZMod m`; the invariants of a
multiplicative group `G` are those of `Additive G`
(`CommGroup.smithAbelianInvariants_additive_eq_iff`). -/
noncomputable def smithAbelianInvariants : List ℕ :=
  (exists_isChain_dvd_addEquiv_pi_zmod G).choose

/-- **The Smith abelian invariants are the unique list of integers larger than `1`, each dividing
the next, such that `A` is the product of the corresponding cyclic groups.** -/
lemma smithAbelianInvariants_eq_iff : smithAbelianInvariants G = L ↔ (∀ m ∈ L, 1 < m) ∧
    L.IsChain (· ∣ ·) ∧ Nonempty (G ≃+ Π i : Fin L.length, ZMod L[i]) := by
  refine ⟨fun h ↦ h ▸ (exists_isChain_dvd_addEquiv_pi_zmod G).choose_spec, fun ⟨hL, hc, ⟨e⟩⟩ ↦ ?_⟩
  rcases (exists_isChain_dvd_addEquiv_pi_zmod G).choose_spec with ⟨hL', hc', ⟨e'⟩⟩
  refine List.reverse_injective <| eq_of_prod_map_gcd_eq (fun m hm ↦ hL' m (List.mem_reverse.mp hm))
    (fun m hm ↦ hL m (List.mem_reverse.mp hm))
    (List.pairwise_reverse.mpr (List.isChain_iff_pairwise.mp hc'))
    (List.pairwise_reverse.mpr (List.isChain_iff_pairwise.mp hc)) fun n ↦ ?_
  rw [List.map_reverse, List.prod_reverse, List.map_reverse, List.prod_reverse]
  exact (prod_map_gcd_eq_card_ker_nsmul n hL' e').trans (prod_map_gcd_eq_card_ker_nsmul n hL e).symm

lemma smithAbelianInvariants_congr (f : G ≃+ H) :
    smithAbelianInvariants G = smithAbelianInvariants H :=
  smithAbelianInvariants_eq_iff.mpr <| (smithAbelianInvariants_eq_iff.mp rfl).imp_right <|
    And.imp_right <| Nonempty.map f.trans

variable (G) in
lemma prod_smithAbelianInvariants : (smithAbelianInvariants G).prod = Nat.card G :=
  (smithAbelianInvariants_eq_iff.mp rfl).2.2.elim prod_eq_card_of_addEquiv

variable (G) in
lemma exists_isPrimePow_pairwise_addEquiv_pi_zmod : ∃ L : List ℕ, (∀ q ∈ L, IsPrimePow q) ∧
    L.Pairwise (fun a b ↦ toLex (a.minFac, a) ≤ toLex (b.minFac, b)) ∧
      Nonempty (G ≃+ Π i : Fin L.length, ZMod L[i]) := by
  classical
  rcases exists_addEquiv_pi_zmod_isPrimePow G with ⟨ι, _, q, hq, ⟨e⟩⟩
  let le : ℕ → ℕ → Bool := fun a b ↦ decide (toLex (a.minFac, a) ≤ toLex (b.minFac, b))
  have hP (x : ℕ) (hx : x ∈ (univ.toList.map q).mergeSort le) : IsPrimePow x := by
    rcases List.mem_map.mp (List.mem_mergeSort.mp hx) with ⟨i, -, rfl⟩
    exact hq i
  refine ⟨_, hP, ?_, nonempty_addEquiv_pi_fin_zmod (fun x hx ↦ (hP x hx).one_lt) fun k ↦ ?_⟩
  · refine (List.pairwise_mergeSort (fun a b c hab hbc ↦ ?_) (fun a b ↦ ?_) _).imp fun h ↦ ?_
    · simp only [le, decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc
    · simpa [le] using le_total _ _
    · simpa [le] using h
  · rw [← prod_gcd_eq_card_ker_nsmul k e (hq · |>.ne_zero),
      ((List.mergeSort_perm _ _).map _).prod_eq, List.map_map, prod_map_toList]
    rfl

variable (G) in
/-- The **primary abelian invariants** of a finite abelian group `A` (LMFDB
`group.abelian_invariants`), or its elementary divisors: the unique list `[q₁, …, qₖ]` of prime
powers `qᵢ = pᵢ ^ eᵢ`, sorted first by `pᵢ` and then increasingly for a fixed `pᵢ`, such that
`A ≃ C_{q₁} × ⋯ × C_{qₖ}` (`AddCommGroup.primaryAbelianInvariants_eq_iff`). This is the primary
decomposition of `A` (LMFDB `group.primary_decomposition`) written in the LMFDB order. Here `C_q`
is `ZMod q`, the prime `pᵢ` is `Nat.minFac qᵢ`, and the invariants of a multiplicative group `G`
are those of `Additive G` (`CommGroup.primaryAbelianInvariants_additive_eq_iff`). -/
noncomputable def primaryAbelianInvariants : List ℕ :=
  (exists_isPrimePow_pairwise_addEquiv_pi_zmod G).choose

/-- **The primary abelian invariants are the unique list of prime powers, sorted first by the prime
and then by size, such that `A` is the product of the corresponding cyclic groups.** -/
lemma primaryAbelianInvariants_eq_iff : primaryAbelianInvariants G = L ↔ (∀ q ∈ L, IsPrimePow q) ∧
    L.Pairwise (fun a b ↦ toLex (a.minFac, a) ≤ toLex (b.minFac, b)) ∧
      Nonempty (G ≃+ Π i : Fin L.length, ZMod L[i]) := by
  refine ⟨fun h ↦ h ▸ (exists_isPrimePow_pairwise_addEquiv_pi_zmod G).choose_spec,
    fun ⟨hL, hs, ⟨e⟩⟩ ↦ ?_⟩
  rcases (exists_isPrimePow_pairwise_addEquiv_pi_zmod G).choose_spec with ⟨hL', hs', ⟨e'⟩⟩
  rcases exists_equiv_of_addEquiv_pi_zmod (fun i ↦ hL' _ (List.getElem_mem i.2))
    (fun j ↦ hL _ (List.getElem_mem j.2)) e' e with ⟨σ, hσ⟩
  refine List.Perm.eq_of_pairwise (fun a b _ _ hab hba ↦ congrArg Prod.snd <|
    toLex.injective <| le_antisymm hab hba) hs' hs <| Multiset.coe_eq_coe.mp ?_
  rw [← map_univ_val_getElem, ← map_univ_val_getElem, ← Multiset.map_univ_val_equiv σ,
    Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ ↦ (hσ i).symm

lemma primaryAbelianInvariants_congr (f : G ≃+ H) :
    primaryAbelianInvariants G = primaryAbelianInvariants H :=
  primaryAbelianInvariants_eq_iff.mpr <| (primaryAbelianInvariants_eq_iff.mp rfl).imp_right <|
    And.imp_right <| Nonempty.map f.trans

variable (G) in
lemma prod_primaryAbelianInvariants : (primaryAbelianInvariants G).prod = Nat.card G :=
  (primaryAbelianInvariants_eq_iff.mp rfl).2.2.elim prod_eq_card_of_addEquiv

end AddCommGroup

namespace CommGroup

open AddCommGroup

variable {G : Type*} [CommGroup G] {L : List ℕ}

private lemma nonempty_addEquiv_iff : Nonempty (Additive G ≃+ Π i : Fin L.length, ZMod L[i]) ↔
    Nonempty (G ≃* Π i : Fin L.length, Multiplicative (ZMod L[i])) :=
  ⟨.map fun e ↦ (AddEquiv.toMultiplicativeRight e).trans (MulEquiv.piMultiplicative _),
    .map fun e ↦ MulEquiv.toAdditiveLeft (e.trans (MulEquiv.piMultiplicative _).symm)⟩

variable [Finite G]

/-- **The Smith abelian invariants of a multiplicative group `G`**, those of `Additive G`, are the
unique list of integers larger than `1`, each dividing the next, such that `G` is the product of
the corresponding multiplicative cyclic groups. -/
lemma smithAbelianInvariants_additive_eq_iff : smithAbelianInvariants (Additive G) = L ↔
    (∀ m ∈ L, 1 < m) ∧ L.IsChain (· ∣ ·) ∧
      Nonempty (G ≃* Π i : Fin L.length, Multiplicative (ZMod L[i])) := by
  rw [smithAbelianInvariants_eq_iff, nonempty_addEquiv_iff]

/-- **The primary abelian invariants of a multiplicative group `G`**, those of `Additive G`, are
the unique list of prime powers, sorted first by the prime and then by size, such that `G` is the
product of the corresponding multiplicative cyclic groups. -/
lemma primaryAbelianInvariants_additive_eq_iff : primaryAbelianInvariants (Additive G) = L ↔
    (∀ q ∈ L, IsPrimePow q) ∧ L.Pairwise (fun a b ↦ toLex (a.minFac, a) ≤ toLex (b.minFac, b)) ∧
      Nonempty (G ≃* Π i : Fin L.length, Multiplicative (ZMod L[i])) := by
  rw [primaryAbelianInvariants_eq_iff, nonempty_addEquiv_iff]

end CommGroup
