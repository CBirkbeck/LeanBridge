import LeanBridge.ForMathlib.GroupTheory.NilpotentSupersolvable
import LeanBridge.ForMathlib.GroupTheory.SolvableSeries
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Metacyclic

/-!
# Supersolvable groups: chains, closure properties and the first classes of examples

A group `G` is supersolvable (LMFDB `group.supersolvable`) if it has a normal series with cyclic
factors. LeanBridge's `Group.IsSupersolvable` allows repeated terms; this file shows that the
series can be taken strictly increasing, as the LMFDB asks, and proves the properties of
supersolvable groups that the knowl states and that do not need representation theory.

The working form of the definition is a chain `⊥ = N 0 ≤ N 1 ≤ ⋯ ≤ N n = ⊤` of normal subgroups of
`G` with `N (i + 1) = ⟨x⟩ N i` for some `x`: a normal subgroup `A ≤ B` has cyclic quotient `B / A`
exactly when `B = ⟨x⟩ A` for some `x`. Images and preimages of such chains under homomorphisms are
chains of the same kind, which gives the closure properties.

## Main results

* `Group.isSupersolvable_iff_exists_strictMono` (LMFDB `group.supersolvable`): a group is
  supersolvable if and only if it has a strictly increasing normal series with cyclic factors.
* `Group.IsSupersolvable.subgroup`, `Group.IsSupersolvable.quotient` (LMFDB
  `group.supersolvable`): subgroups and quotients of supersolvable groups are supersolvable.
* `Group.IsSupersolvable.of_ker_eq_zpowers`: a group with a homomorphism to a supersolvable group
  whose kernel is cyclic is supersolvable. In particular an extension of a supersolvable group by
  a cyclic normal subgroup is supersolvable, `Group.IsSupersolvable.of_quotient_zpowers`.
* `Group.IsSupersolvable.isSolvable` (LMFDB `group.supersolvable`): supersolvable groups are
  solvable.
* `Group.IsSupersolvable.exists_ne_one_normal_zpowers`: a nontrivial supersolvable group has a
  nontrivial cyclic normal subgroup.
* `Group.IsSupersolvable.exists_notMem_normal_zpowers_sup`: above a proper normal subgroup `Z`
  with supersolvable quotient lies a normal subgroup `⟨x⟩ Z` with `x ∉ Z`.
* `Group.IsSupersolvable.index_prime_of_isCoatom` (LMFDB `group.supersolvable`): every maximal
  subgroup of a finite supersolvable group has prime index, one direction of Huppert's criterion.
* `Group.isSupersolvable_of_isMulCommutative`, `IsZGroup.isSupersolvable`,
  `Group.isSupersolvable_of_squarefree_card` (LMFDB `group.supersolvable`): finite abelian groups,
  finite Z-groups and groups of squarefree order are supersolvable.
-/

open Function Group Subgroup

variable {G H : Type*} [Group G] [Group H]

namespace Subgroup

variable {A B : Subgroup G} [A.Normal]

lemma isCyclic_quotient_subgroupOf_iff (hAB : A ≤ B) :
    IsCyclic (B ⧸ A.subgroupOf B) ↔ ∃ x, B = zpowers x ⊔ A := by
  refine ⟨fun ⟨⟨q, hq⟩⟩ ↦ ?_, fun ⟨x, hx⟩ ↦ isCyclic_quotient_of_eq_sup
    (normalizer_eq_top_iff.mpr ‹A.Normal› ▸ mem_top x) (hx ▸ mem_sup_left (mem_zpowers x)) hx⟩
  rcases QuotientGroup.mk_surjective q with ⟨⟨x, hxB⟩, rfl⟩
  refine ⟨x, le_antisymm (fun y hy ↦ ?_) (sup_le (zpowers_le.mpr hxB) hAB)⟩
  rcases hq (QuotientGroup.mk ⟨y, hy⟩) with ⟨m, hm⟩
  have hmem : (x ^ m)⁻¹ * y ∈ A := by
    simpa [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf] using hm
  simpa using mul_mem_sup (zpow_mem (mem_zpowers x) m) hmem

lemma exists_comap_eq_zpowers_sup (f : H →* G) (h : ∃ x, B = zpowers x ⊔ A) :
    ∃ y, B.comap f = zpowers y ⊔ A.comap f := by
  rcases h with ⟨x, rfl⟩
  have hc : IsCyclic (↥(zpowers x ⊔ A) ⧸ A.subgroupOf (zpowers x ⊔ A)) :=
    (isCyclic_quotient_subgroupOf_iff le_sup_right).mpr ⟨x, rfl⟩
  refine (isCyclic_quotient_subgroupOf_iff <| comap_mono le_sup_right).mp ?_
  let φ : ↥((zpowers x ⊔ A).comap f) ⧸ (A.comap f).subgroupOf ((zpowers x ⊔ A).comap f) →*
      ↥(zpowers x ⊔ A) ⧸ A.subgroupOf (zpowers x ⊔ A) :=
    QuotientGroup.map _ _ (f.subgroupComap (zpowers x ⊔ A)) fun _ hy ↦ hy
  refine isCyclic_of_injective φ <| (injective_iff_map_eq_one φ).mpr fun q hq ↦ ?_
  rcases QuotientGroup.mk_surjective q with ⟨y, rfl⟩
  exact (QuotientGroup.eq_one_iff y).mpr <|
    (QuotientGroup.eq_one_iff <| f.subgroupComap (zpowers x ⊔ A) y).mp hq

lemma normal_zpowers_pow {x : G} (hx : (zpowers x).Normal) (m : ℕ) : (zpowers (x ^ m)).Normal :=
  ⟨fun z hz g ↦ by
    rcases mem_zpowers_iff.mp hz with ⟨j, rfl⟩
    rcases mem_zpowers_iff.mp <| hx.conj_mem x (mem_zpowers x) g with ⟨k, hk⟩
    refine mem_zpowers_iff.mpr ⟨k * j, ?_⟩
    rw [← conj_zpow, ← conj_pow, ← hk, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      ← zpow_mul, mul_left_comm]⟩

lemma isCoatom_map_mk' (hB : IsCoatom B) (hAB : A ≤ B) :
    IsCoatom (B.map (QuotientGroup.mk' A)) := by
  have hc : (B.map (QuotientGroup.mk' A)).comap (QuotientGroup.mk' A) = B :=
    comap_map_eq_self <| (QuotientGroup.ker_mk' A).trans_le hAB
  refine ⟨fun h ↦ hB.1 ?_, fun K hK ↦ ?_⟩
  · rw [← hc, h, comap_top]
  · have hlt : B < K.comap (QuotientGroup.mk' A) :=
      hc ▸ (comap_lt_comap_of_surjective <| QuotientGroup.mk'_surjective A).mpr hK
    rw [← map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A) K, hB.2 _ hlt,
      map_top_of_surjective _ <| QuotientGroup.mk'_surjective A]

end Subgroup

namespace Group

lemma isSupersolvable_iff_exists_chain : IsSupersolvable G ↔ ∃ (n : ℕ) (N : ℕ → Subgroup G),
    N 0 = ⊥ ∧ N n = ⊤ ∧ (∀ i, (N i).Normal) ∧ ∀ i < n, ∃ x, N (i + 1) = zpowers x ⊔ N i := by
  refine ⟨fun ⟨s, hs⟩ ↦ ⟨s.length, fun i ↦ s ⟨min i s.length, by omega⟩, ?_, ?_, fun i ↦ s.normal _,
    fun i hi ↦ ?_⟩, fun ⟨n, N, h0, hn, hN, h⟩ ↦ ?_⟩
  · exact (congrArg s.toFun <| Fin.ext <| Nat.zero_min _).trans s.head_eq_bot
  · exact (congrArg s.toFun <| Fin.ext <| min_self _).trans s.last_eq_top
  · have h₁ : (⟨min (i + 1) s.length, by omega⟩ : Fin (s.length + 1)) = Fin.succ ⟨i, hi⟩ :=
      Fin.ext <| min_eq_left hi
    have h₀ : (⟨min i s.length, by omega⟩ : Fin (s.length + 1)) = Fin.castSucc ⟨i, hi⟩ :=
      Fin.ext <| min_eq_left hi.le
    have : (s.toFun (Fin.castSucc ⟨i, hi⟩)).Normal := s.normal _
    dsimp only
    rw [h₁, h₀]
    exact (isCyclic_quotient_subgroupOf_iff <| s.le_succ ⟨i, hi⟩).mp <| hs ⟨i, hi⟩
  · have hle (i : Fin n) : N i ≤ N (i + 1) := by
      rcases h i i.2 with ⟨x, hx⟩
      exact hx ▸ le_sup_right
    refine ⟨NormalSeries.ofLE ⟨n, fun i ↦ N i, hle⟩ (fun i ↦ hN i) h0 hn, fun i ↦ ?_⟩
    have : (N i).Normal := hN i
    exact (isCyclic_quotient_subgroupOf_iff <| hle i).mpr <| h i i.2

/-- **A group is supersolvable if and only if it has a strictly increasing normal series with
cyclic factors** (LMFDB `group.supersolvable`): the LMFDB's definition, with strict inclusions
`{1} = N₀ < N₁ < ⋯ < Nₖ = G`, agrees with `Group.IsSupersolvable`, which allows repeated terms. A
series of least length has no repeated term, since a repeated term can be left out. -/
lemma isSupersolvable_iff_exists_strictMono :
    IsSupersolvable G ↔ ∃ s : NormalSeries G, StrictMono s ∧ s.IsPolycyclic := by
  refine ⟨fun hG ↦ ?_, fun ⟨s, _, hs⟩ ↦ ⟨s, hs⟩⟩
  classical
  have hP : ∃ n, ∃ N : ℕ → Subgroup G, N 0 = ⊥ ∧ N n = ⊤ ∧ (∀ i, (N i).Normal) ∧
      ∀ i < n, ∃ x, N (i + 1) = zpowers x ⊔ N i :=
    isSupersolvable_iff_exists_chain.mp hG
  rcases Nat.find_spec hP with ⟨N, h0, hn, hN, h⟩
  have hlt (i : ℕ) (hi : i < Nat.find hP) : N i < N (i + 1) := by
    rcases h i hi with ⟨x, hx⟩
    refine (le_sup_right.trans_eq hx.symm).lt_of_ne fun heq ↦ Nat.find_min hP
      (Nat.sub_one_lt <| Nat.ne_zero_of_lt hi) ⟨fun j ↦ if j ≤ i then N j else N (j + 1), ?_, ?_,
      fun j ↦ ?_, fun j hj ↦ ?_⟩
    · simpa using h0
    · dsimp only
      split_ifs
      · rw [show Nat.find hP - 1 = i by omega, heq, show i + 1 = Nat.find hP by omega, hn]
      · rw [show Nat.find hP - 1 + 1 = Nat.find hP by omega, hn]
    · dsimp only
      split_ifs <;> exact hN _
    · rcases lt_trichotomy j i with hji | rfl | hji
      · simpa [show j + 1 ≤ i by omega, hji.le] using h j <| by omega
      · simpa [heq] using h (j + 1) <| by omega
      · simpa [show ¬j + 1 ≤ i by omega, show ¬j ≤ i by omega] using h (j + 1) <| by omega
  refine ⟨NormalSeries.ofLE ⟨Nat.find hP, fun i ↦ N i, fun i ↦ (hlt i i.2).le⟩ (fun i ↦ hN i) h0 hn,
    Fin.strictMono_iff_lt_succ.mpr fun i ↦ hlt i i.2, fun i ↦ ?_⟩
  have : (N i).Normal := hN i
  exact (isCyclic_quotient_subgroupOf_iff (hlt i i.2).le).mpr <| h i i.2

namespace IsSupersolvable

lemma of_surjective (hG : IsSupersolvable G) {f : G →* H} (hf : Surjective f) :
    IsSupersolvable H := by
  rcases isSupersolvable_iff_exists_chain.mp hG with ⟨n, N, h0, hn, hN, h⟩
  refine isSupersolvable_iff_exists_chain.mpr ⟨n, fun i ↦ (N i).map f,
    by simp only [h0, Subgroup.map_bot], by simp only [hn, map_top_of_surjective f hf],
    fun i ↦ (hN i).map f hf, fun i hi ↦ ?_⟩
  rcases h i hi with ⟨x, hx⟩
  exact ⟨f x, by simp only [hx, Subgroup.map_sup, f.map_zpowers]⟩

/-- **A group with a homomorphism to a supersolvable group whose kernel is cyclic is
supersolvable**: the preimages of a normal series with cyclic factors, with the trivial subgroup
put in front, form such a series. -/
lemma of_ker_eq_zpowers (hG : IsSupersolvable G) {f : H →* G} {c : H} (hc : f.ker = zpowers c) :
    IsSupersolvable H := by
  rcases isSupersolvable_iff_exists_chain.mp hG with ⟨n, N, h0, hn, hN, h⟩
  refine isSupersolvable_iff_exists_chain.mpr ⟨n + 1,
    fun i ↦ if i = 0 then ⊥ else (N (i - 1)).comap f, ite_eq_left rfl, by simp [hn], fun i ↦ ?_,
    fun i hi ↦ ?_⟩
  · dsimp only
    split_ifs
    exacts [inferInstance, (hN _).comap f]
  · rcases i with _ | i
    · exact ⟨c, by simp [h0, hc]⟩
    · have : (N i).Normal := hN i
      simpa using exists_comap_eq_zpowers_sup f <| h i <| by omega

lemma of_injective (hG : IsSupersolvable G) {f : H →* G} (hf : Injective f) : IsSupersolvable H :=
  hG.of_ker_eq_zpowers <| (f.ker_eq_bot_iff.mpr hf).trans zpowers_one_eq_bot.symm

/-- **Subgroups of supersolvable groups are supersolvable** (LMFDB `group.supersolvable`). -/
lemma subgroup (hG : IsSupersolvable G) (K : Subgroup G) : IsSupersolvable K :=
  hG.of_injective K.subtype_injective

/-- **Quotients of supersolvable groups are supersolvable** (LMFDB `group.supersolvable`). -/
lemma quotient (hG : IsSupersolvable G) (K : Subgroup G) [K.Normal] : IsSupersolvable (G ⧸ K) :=
  hG.of_surjective <| QuotientGroup.mk'_surjective K

/-- **An extension of a supersolvable group by a cyclic normal subgroup is supersolvable**: if
`⟨c⟩` is normal in `G` and `G ⧸ ⟨c⟩` is supersolvable, then so is `G`. -/
lemma of_quotient_zpowers {c : G} [(zpowers c).Normal] (hG : IsSupersolvable (G ⧸ zpowers c)) :
    IsSupersolvable G :=
  hG.of_ker_eq_zpowers <| QuotientGroup.ker_mk' _

/-- **Supersolvable groups are solvable** (LMFDB `group.supersolvable`): a normal series with
cyclic factors is a subnormal series with abelian factors, which makes a group solvable by
`Group.isSolvable_iff_exists_subnormalSeries` (LMFDB `group.solvable`). -/
lemma isSolvable (hG : IsSupersolvable G) : IsSolvable G := by
  rcases hG with ⟨s, hs⟩
  exact isSolvable_iff_exists_subnormalSeries.mpr ⟨s.toSubnormalSeries, fun i ↦
    have : IsCyclic (s.factor i) := hs i
    inferInstance⟩

/-- **A nontrivial supersolvable group has a nontrivial cyclic normal subgroup**, the first
nontrivial term of a normal series with cyclic factors. -/
lemma exists_ne_one_normal_zpowers [Nontrivial G] (hG : IsSupersolvable G) :
    ∃ x : G, x ≠ 1 ∧ (zpowers x).Normal := by
  rcases isSupersolvable_iff_exists_chain.mp hG with ⟨n, N, h0, hn, hN, h⟩
  have key (i : ℕ) : i ≤ n → N i = ⊥ ∨ ∃ x : G, x ≠ 1 ∧ (zpowers x).Normal := by
    induction i with
    | zero => exact fun _ ↦ .inl h0
    | succ i ih =>
      intro hi
      rcases ih <| by omega with hi' | hi'
      · rcases h i <| by omega with ⟨x, hx⟩
        rw [hi', sup_bot_eq] at hx
        rcases eq_or_ne x 1 with rfl | hx1
        · exact .inl <| hx.trans zpowers_one_eq_bot
        · exact .inr ⟨x, hx1, hx ▸ hN (i + 1)⟩
      · exact .inr hi'
  exact (key n le_rfl).resolve_left <| hn ▸ top_ne_bot

/-- **Above a proper normal subgroup `Z` with supersolvable quotient lies a normal subgroup `⟨x⟩ Z`
with `x ∉ Z`**, the preimage of a nontrivial cyclic normal subgroup of `G ⧸ Z`. For a
supersolvable group `G` this holds for every proper normal subgroup `Z`, which is the criterion
used to show that a given group is not supersolvable. -/
lemma exists_notMem_normal_zpowers_sup {Z : Subgroup G} [Z.Normal] (hG : IsSupersolvable (G ⧸ Z))
    (hZ : Z ≠ ⊤) : ∃ x ∉ Z, (zpowers x ⊔ Z).Normal := by
  have : Nontrivial (G ⧸ Z) := QuotientGroup.nontrivial_iff.mpr hZ
  rcases hG.exists_ne_one_normal_zpowers with ⟨q, hq1, hqn⟩
  rcases QuotientGroup.mk_surjective q with ⟨x, rfl⟩
  refine ⟨x, fun hx ↦ hq1 <| (QuotientGroup.eq_one_iff x).mpr hx, ?_⟩
  rw [sup_comm, ← QuotientGroup.comap_map_mk', (QuotientGroup.mk' Z).map_zpowers]
  exact hqn.comap _

/-- **In a finite supersolvable group every maximal subgroup has prime index** (LMFDB
`group.supersolvable`), one direction of Huppert's criterion. A normal subgroup `N` of prime order
`p` either lies in the maximal subgroup `M`, and induction applies to `G ⧸ N`, or `G = M N` and
`M ∩ N = 1`, so that `M` has index `p`. -/
lemma index_prime_of_isCoatom [Finite G] (hG : IsSupersolvable G) {M : Subgroup G}
    (hM : IsCoatom M) : M.index.Prime := by
  rcases (⟨_, rfl⟩ : ∃ n, Nat.card G = n) with ⟨n, hn⟩
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  have : Nontrivial G := by
    rcases IsConcreteLE.exists_of_lt <| lt_top_iff_ne_top.mpr hM.1 with ⟨g, -, hg⟩
    exact nontrivial_of_ne g 1 fun h ↦ hg <| h ▸ one_mem M
  rcases hG.exists_ne_one_normal_zpowers with ⟨x, hx1, hx⟩
  rcases Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.mpr hx1) with ⟨p, hp, hpx⟩
  let N : Subgroup G := zpowers (x ^ (orderOf x / p))
  have : N.Normal := normal_zpowers_pow hx _
  have hN : Nat.card N = p :=
    (Nat.card_zpowers _).trans <| orderOf_pow_orderOf_div (orderOf_pos x).ne' hpx
  have hNG : p * N.index = n := hN ▸ hn ▸ N.card_mul_index
  by_cases hNM : N ≤ M
  · rw [← index_map_eq _ (QuotientGroup.mk'_surjective N) <|
      (QuotientGroup.ker_mk' N).trans_le hNM]
    refine ih _ ?_ (hG.quotient N) (isCoatom_map_mk' hM hNM) rfl
    have : 0 < N.index := Nat.pos_of_ne_zero N.index_ne_zero_of_finite
    rw [← index_eq_card]
    nlinarith [hp.two_le]
  · have hsup : M ⊔ N = ⊤ :=
      hM.2 _ <| le_sup_left.lt_of_ne fun h ↦ hNM <| h ▸ le_sup_right
    have hinf : N ⊓ M = ⊥ := by
      rcases (Nat.dvd_prime hp).mp <| hN ▸ card_dvd_of_le (inf_le_left : N ⊓ M ≤ N) with h | h
      · exact card_eq_one.mp h
      · exact absurd ((eq_of_le_of_card_ge inf_le_left (hN.trans h.symm).le) ▸ inf_le_right) hNM
    have hMN : N.index = Nat.card M := by
      rw [← relIndex_top_right, ← hsup, relIndex_sup_right, ← inf_relIndex_right, hinf,
        relIndex_bot_left]
    have hM' : Nat.card M * M.index = n := hn ▸ M.card_mul_index
    rw [← hMN, ← hNG, mul_comm] at hM'
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero N.index_ne_zero_of_finite) hM') ▸ hp

end IsSupersolvable

/-- **Finite abelian groups are supersolvable** (LMFDB `group.supersolvable`), being nilpotent. -/
lemma isSupersolvable_of_isMulCommutative [Finite G] [IsMulCommutative G] : IsSupersolvable G :=
  IsNilpotent.isSupersolvable

lemma isSupersolvable_of_subsingleton [Subsingleton G] : IsSupersolvable G :=
  IsNilpotent.isSupersolvable

end Group

/-- **Finite Z-groups are supersolvable** (LMFDB `group.supersolvable`, `group.z_group`), being
metacyclic. -/
lemma IsZGroup.isSupersolvable [Finite G] [IsZGroup G] : IsSupersolvable G :=
  have : IsMetacyclic G := IsZGroup.isMetacyclic
  IsMetacyclic.isSupersolvable

/-- **Groups of squarefree order are supersolvable** (LMFDB `group.supersolvable`), being
Z-groups. -/
lemma Group.isSupersolvable_of_squarefree_card (h : Squarefree (Nat.card G)) : IsSupersolvable G :=
  have : Finite G := Nat.finite_of_card_ne_zero h.ne_zero
  have : IsZGroup G := IsZGroup.of_squarefree h
  IsZGroup.isSupersolvable
