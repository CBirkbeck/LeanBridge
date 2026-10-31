import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamily
import LeanBridge.ForMathlib.NumberTheory.LocalField.WildArtinSlopes
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient
import TauCeti.NumberTheory.LocalField.TamelyRamified.Basic

/-!
# Swan slopes, rams and Herbrand invariants of non-Galois extensions, after Deligne

Let `L / K` be a finite separable extension of nonarchimedean local fields of residue
characteristic `p`, contained in a finite Galois extension `M / K` with group `G`, lower
ramification groups `G_i`, upper ramification groups `G^v` and Herbrand function `φ_{M/K}`, and let
`H = Gal(M / L)`. Deligne (appendix to *Les corps locaux de caractéristique p, limites de corps
locaux de caractéristique 0*) attaches upper ramification breaks to `L / K` through the action of
the upper ramification groups on the `G`-set `Hom_K(L, M) ≅ G / H`: the normal subgroup `G^v` has
orbits of `n^v = [G^v : G^v ∩ H]` elements, and the **Swan slopes** of `L / K` (LMFDB
`lf.swan_slopes`) are the `v > 0` at which `n^v` drops, a drop by the factor `p ^ m` giving the
slope `v` with multiplicity `m`. Since `G^{φ(i)} = G_i` and `G^v = G_{i + 1}` for
`φ(i) < v ≤ φ(i + 1)`, they are the `φ_{M/K}(i)` for the integers `i ≥ 1`, repeated
`log_p (n_i / n_{i + 1})` times for `n_i = [G_i : G_i ∩ H]`, which is how `swanSlopesOfSubgroup`
defines them, for any subgroup `H` of `G`. LeanBridge's
`IsNonarchimedeanLocalField.visibleSwanSlopes` is this definition for the Galois closure of `L` in
`K̄`.

We prove that this definition is Deligne's: `n^v = p ^ N(v)` for every `v > 0`, where `N(v)` is the
number of Swan slopes `≥ v` counted with multiplicity, and a multiset of positive reals is
determined by these counts. With Herbrand's theorem `G^v ↦ (G / N)^v` (Tau Ceti), this shows that
the Swan slopes do not depend on the Galois extension `M` containing `L`, and that for `L / K`
Galois they are the Swan slopes `IsNonarchimedeanLocalField.swanSlopesOfIsGalois` of `L / K`. There
are `v_p([G_0 : G_0 ∩ H]) = v_p(e(L / K))` of them.

The **rams** (LMFDB `lf.rams`) of `L / K` are the corresponding lower breaks: Deligne's Herbrand
function of `L / K` is `φ_{L/K} = φ_{M/K} ∘ ψ_{M/L}`, and the rams are the `ψ_{L/K}(s)` for the
Swan slopes `s`, that is the `φ_{M/L}(i) = (#H_1 + ⋯ + #H_i) / #H_0` with `H_j = H ∩ G_j`, with the
same multiplicities. They are rational, as the LMFDB states, and they do not depend on `M` either,
since `φ_{L/K}` does not. The **Herbrand invariant** `(r_1, …, r_w)_ε^f` (LMFDB
`lf.herbrand_invariant`) of `L / K` collects its rams in increasing order, the prime-to-`p` part `ε`
of its ramification index and its residue degree `f`, and `e(L / K) = ε p ^ w`; its small and tiny
rams (LMFDB `lf.rams`) are those of this invariant. The Swan slopes
`s_k = ∑_{j < k} (r_{j + 1} - r_j) / (ε p ^ j)` of the invariant, computed from the rams by LMFDB's
formula, are the Swan slopes of `L / K`: `φ_{L/K}` has slope `1 / (ε p ^ k)` between `r_k` and
`r_{k + 1}`, because `[G_i : G_i ∩ H] = p ^ (w - k)` there and `[G_0 : G_0 ∩ H] = ε p ^ w`. So the
three representations of LMFDB `lf.herbrand_invariant` agree, and every finite extension of a
`p`-adic field inside `K̄` lies in the family of its Herbrand invariant.

## Main definitions

* `IsNonarchimedeanLocalField.swanSlopesOfSubgroup` (LMFDB `lf.swan_slopes`): the Swan slopes of
  `G / H`, Deligne's positive upper breaks.
* `IsNonarchimedeanLocalField.herbrandOfSubgroup`: the Herbrand function `φ_{M/M^H}` at an integer.
* `IsNonarchimedeanLocalField.ramsOfSubgroup` (LMFDB `lf.rams`): the rams of `G / H`.
* `IsNonarchimedeanLocalField.herbrandOfTower`: Deligne's Herbrand function
  `φ_{L/K} = φ_{M/K} ∘ ψ_{M/L}` of a tower `M / L / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ofRams`: the Herbrand invariant with given rams,
  ramification index and residue degree.
* `IsNonarchimedeanLocalField.herbrandInvariantOfTower` (LMFDB `lf.herbrand_invariant`, `lf.rams`):
  the Herbrand invariant of `L / K`, computed in `M`.
* `IsNonarchimedeanLocalField.visibleRams` (LMFDB `lf.rams`): the rams of a finite separable
  extension of `K` inside `K̄`.
* `IsNonarchimedeanLocalField.visibleHerbrandInvariant` (LMFDB `lf.herbrand_invariant`, `lf.rams`):
  the Herbrand invariant of a finite separable extension of `K` inside `K̄`.

## Main theorems

* `IsNonarchimedeanLocalField.relIndex_upperRamificationGroup_eq_pow_countP`: Deligne's
  description, `[G^v : G^v ∩ H] = p ^ N(v)` for `v > 0`.
* `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_comap_restrictNormalHom`: the Swan slopes do not
  depend on the Galois extension `M`.
* `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_bot`,
  `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_ker_restrictNormalHom` and
  `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_range_restrictScalarsHom_of_isGalois`: for
  `L / K` Galois they are the Swan slopes of the Galois extension `L / K`.
* `IsNonarchimedeanLocalField.card_swanSlopesOfSubgroup`: there are `v_p([G_0 : G_0 ∩ H])` of them.
* `IsNonarchimedeanLocalField.relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom` and
  `IsNonarchimedeanLocalField.card_swanSlopesOfSubgroup_range_restrictScalarsHom`:
  `[G_0 : G_0 ∩ H] = e(L / K)`, so `L / K` has `v_p(e(L / K))` Swan slopes.
* `IsNonarchimedeanLocalField.ramsOfSubgroup_bot` and
  `IsNonarchimedeanLocalField.ramsOfSubgroup_range_restrictScalarsHom_of_isGalois`: for `L / K`
  Galois the rams are the rams `IsNonarchimedeanLocalField.ramsOfIsGalois` of `L / K`.
* `IsNonarchimedeanLocalField.herbrandOfSubgroup_range_restrictScalarsHom`: in a tower `M / L / K`,
  `IsNonarchimedeanLocalField.herbrandOfSubgroup` is Tau Ceti's Herbrand function `φ_{M/L}`.
* `IsNonarchimedeanLocalField.swanSlopesOfSubgroup_eq_map_herbrandOfTower`: the Swan slopes are the
  images of the rams under `φ_{L/K}`.
* `IsNonarchimedeanLocalField.herbrandOfTower_eq_herbrandOfTower`,
  `IsNonarchimedeanLocalField.ramsOfSubgroup_range_restrictScalarsHom_eq` and
  `IsNonarchimedeanLocalField.herbrandInvariantOfTower_eq`: `φ_{L/K}`, the rams and the Herbrand
  invariant of `L / K` do not depend on the Galois extension `M`.
* `IsNonarchimedeanLocalField.ε_mul_pow_w_herbrandInvariantOfTower`: `e(L / K) = ε p ^ w`.
* `IsNonarchimedeanLocalField.map_swanSlope_ofRams` and
  `IsNonarchimedeanLocalField.map_swanSlope_herbrandInvariantOfTower`: the Swan slopes of the
  Herbrand invariant, computed from its rams, are the Swan slopes of `L / K`.
* `IsNonarchimedeanLocalField.isInvariantOf_visibleHerbrandInvariant`: an extension of a `p`-adic
  field inside `K̄` has Herbrand invariant `IsNonarchimedeanLocalField.visibleHerbrandInvariant`, in
  the sense of `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf`, and
  `IsNonarchimedeanLocalField.mk_mem_family_visibleHerbrandInvariant`: it lies in the family `I / K`
  of its Herbrand invariant `I`.
* `IsNonarchimedeanLocalField.visibleSwanSlopes_eq_swanSlopesOfSubgroup`: LeanBridge's
  `IsNonarchimedeanLocalField.visibleSwanSlopes` are these Swan slopes.
* `IsNonarchimedeanLocalField.card_visibleSwanSlopes` and
  `IsNonarchimedeanLocalField.ε_mul_pow_w_visibleHerbrandInvariant`: an extension `L / K` inside
  `K̄` has `v_p(e(L / K))` Swan slopes, and `e(L / K) = ε p ^ w`.
* `IsNonarchimedeanLocalField.visibleSwanSlopes_eq_swanSlopesOfIsGalois` and
  `IsNonarchimedeanLocalField.visibleRams_eq_ramsOfIsGalois`: for `L / K` Galois inside `K̄`, the
  Swan slopes and rams are those of the Galois extension `L / K`.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

namespace IsNonarchimedeanLocalField

variable {S : Multiset ℝ}

lemma eq_pow_sum_padicValNat_div (p : ℕ) [hp : Fact p.Prime] (a : ℕ → ℕ) (T : ℕ)
    (h₁ : ∀ i, 1 ≤ i → ∃ k, a i = p ^ k) (h₂ : ∀ i, a (i + 1) ≤ a i) (h₃ : a (T + 1) = 1) {j : ℕ}
    (hj : 1 ≤ j) :
    a j = p ^ ∑ i ∈ range T, if j ≤ i + 1 then padicValNat p (a (i + 1) / a (i + 2)) else 0 := by
  generalize hjT : T + 1 - j = n
  induction n generalizing j with
  | zero =>
    rw [sum_eq_zero fun i hi ↦ ite_eq_right (by simp at hi; omega), pow_zero]
    rcases h₁ j hj with ⟨k, hk⟩
    have h : a j ≤ a (T + 1) := antitone_nat_of_succ_le h₂ (by omega)
    rw [h₃, hk] at h
    exact hk.trans <| le_antisymm h <| Nat.one_le_pow _ _ hp.out.pos
  | succ n ih =>
    rw [sum_congr rfl fun i _ ↦ (by split_ifs <;> omega : (if j ≤ i + 1 then
      padicValNat p (a (i + 1) / a (i + 2)) else 0) = (if j + 1 ≤ i + 1 then
      padicValNat p (a (i + 1) / a (i + 2)) else 0) + if i = j - 1 then
      padicValNat p (a (i + 1) / a (i + 2)) else 0), sum_add_distrib, sum_ite_eq',
      ite_eq_left (mem_range.mpr (by omega)), pow_add, ← ih (by omega) (by omega),
      Nat.sub_add_cancel hj, (by omega : j - 1 + 2 = j + 1)]
    rcases h₁ j hj with ⟨k, hk⟩
    rcases h₁ (j + 1) (by omega) with ⟨l, hl⟩
    have hlk : l ≤ k := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp (hk ▸ hl ▸ h₂ j)
    rw [hk, hl, Nat.pow_div hlk hp.out.pos, padicValNat.prime_pow, ← pow_add,
      Nat.add_sub_of_le hlk]

lemma countP_le_eq_count_add_countP_le {U : Multiset ℝ} {a b : ℝ} (hab : a < b)
    (hU : ∀ x ∈ U, a < x → b ≤ x) : U.countP (a ≤ ·) = U.count a + U.countP (b ≤ ·) := by
  induction U using Multiset.induction_on with
  | empty => simp
  | cons x U ih =>
    rw [Multiset.countP_cons, Multiset.count_cons, Multiset.countP_cons,
      ih fun y hy ↦ hU y (Multiset.mem_cons_of_mem hy)]
    have hx : a < x → b ≤ x := hU x (Multiset.mem_cons_self x U)
    rcases lt_trichotomy x a with h | rfl | h
    · rw [ite_eq_right h.not_ge, ite_eq_right h.ne', ite_eq_right (h.trans hab).not_ge]
      omega
    · rw [ite_eq_left le_rfl, ite_eq_left rfl, ite_eq_right hab.not_ge]
      omega
    · rw [ite_eq_left h.le, ite_eq_right h.ne, ite_eq_left (hx h)]
      omega

lemma eq_of_countP_le_eq {T : Multiset ℝ} (hS : ∀ x ∈ S, 0 < x) (hT : ∀ x ∈ T, 0 < x)
    (h : ∀ v : ℝ, 0 < v → S.countP (v ≤ ·) = T.countP (v ≤ ·)) : S = T := by
  ext a
  rcases le_or_gt a 0 with ha | ha
  · rw [Multiset.count_eq_zero_of_notMem fun h ↦ (hS a h).not_ge ha,
      Multiset.count_eq_zero_of_notMem fun h ↦ (hT a h).not_ge ha]
  have hb : ∃ b, a < b ∧ ∀ x ∈ S + T, a < x → b ≤ x := by
    by_cases hF : ((S + T).toFinset.filter (a < ·)).Nonempty
    · refine ⟨_, (mem_filter.mp (min'_mem _ hF)).2, fun x hx hax ↦ min'_le _ x ?_⟩
      rw [mem_filter, Multiset.mem_toFinset]
      exact ⟨hx, hax⟩
    · refine ⟨a + 1, lt_add_one a, fun x hx hax ↦ (hF ⟨x, ?_⟩).elim⟩
      rw [mem_filter, Multiset.mem_toFinset]
      exact ⟨hx, hax⟩
  rcases hb with ⟨b, hab, hb⟩
  have h₁ : S.countP (a ≤ ·) = S.count a + S.countP (b ≤ ·) :=
    countP_le_eq_count_add_countP_le hab fun x hx ↦ hb x (Multiset.mem_add.mpr (.inl hx))
  have h₂ : T.countP (a ≤ ·) = T.count a + T.countP (b ≤ ·) :=
    countP_le_eq_count_add_countP_le hab fun x hx ↦ hb x (Multiset.mem_add.mpr (.inr hx))
  rw [h a ha, h b (ha.trans hab)] at h₁
  omega

variable {l : List ℚ} (a : ℚ) {k : ℕ}

lemma getElem_le_of_lt_countP (hl : l.Pairwise (· ≤ ·)) (hk : k < l.length)
    (hm : k < l.countP (· ≤ a)) : l[k] ≤ a := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.countP_cons] at hm
    rcases k with _ | k
    · by_contra h
      have h' : l.countP (· ≤ a) = 0 := List.countP_eq_zero.mpr fun y hy hya ↦ h <|
        (hl.1 y hy).trans (by simpa using hya)
      simp only [List.getElem_cons_zero] at h
      simp [h', h] at hm
    · exact ih hl.2 (by simpa using hk) (by split_ifs at hm <;> omega)

lemma lt_getElem_of_countP_le (hl : l.Pairwise (· ≤ ·)) (hk : k < l.length)
    (hm : l.countP (· ≤ a) ≤ k) : a < l[k] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x l ih =>
    rw [List.pairwise_cons] at hl
    rw [List.countP_cons] at hm
    by_cases hx : x ≤ a
    · rcases k with _ | k
      · simp [hx] at hm
      · exact ih hl.2 (by simpa using hk) (by simp [hx] at hm; omega)
    · rcases k with _ | k
      · simpa using hx
      · exact (not_le.mp hx).trans_le (hl.1 _ (List.getElem_mem _))

lemma fixingSubgroup_preimage_eq_range_restrictScalarsHom {F Ω : Type*} [Field F] [Field Ω]
    [Algebra F Ω] {L E : IntermediateField F Ω} (h : L ≤ E) :
    letI : Algebra L E := (IntermediateField.inclusion h).toAlgebra
    haveI : IsScalarTower F L E := .of_algebraMap_eq fun _ ↦ rfl
    fixingSubgroup (E ≃ₐ[F] E) (((↑) : E → Ω) ⁻¹' L) =
      (AlgEquiv.restrictScalarsHom (S := L) F).range := by
  let a : Algebra L E := (IntermediateField.inclusion h).toAlgebra
  have hs : IsScalarTower F L E := .of_algebraMap_eq fun _ ↦ rfl
  ext σ
  rw [mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · intro hσ
    exact ⟨({ σ with commutes' := fun l ↦ hσ _ l.2 } : E ≃ₐ[L] E), AlgEquiv.ext fun _ ↦ rfl⟩
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes ⟨x, hx⟩

namespace HerbrandInvariant

variable (p : ℕ) (hp : p.Prime) (R : Multiset ℚ) (hR : ∀ r ∈ R, 0 < r) (e f : ℕ) (he : e ≠ 0)
  (hf : 0 < f)

/-- The **Herbrand invariant** `(r_1, …, r_w)_ε^f` at a prime `p` (LMFDB `lf.herbrand_invariant`)
whose rams `r_1 ≤ ⋯ ≤ r_w` are the elements of a multiset `R` of positive rationals in increasing
order, so that `w` is the cardinality of `R`, with `ε` the prime-to-`p` part of a positive integer
`e` (the ramification index `ε p ^ w` when `e` has `p`-adic valuation `w`) and residue degree
`f > 0`. -/
noncomputable def ofRams : HerbrandInvariant p where
  w := Multiset.card R
  ram k := if k = 0 then 0 else (R.sort (· ≤ ·)).getD (min k (Multiset.card R) - 1) 0
  ε := ordCompl[p] e
  f := f
  ram_zero := rfl
  zero_lt_ram_one hw := by
    have h : min 1 (Multiset.card R) - 1 < (R.sort (· ≤ ·)).length := by
      rw [Multiset.length_sort]
      omega
    rw [ite_eq_right one_ne_zero, List.getD_eq_getElem _ _ h]
    exact hR _ ((Multiset.mem_sort _).mp (List.getElem_mem h))
  monotone_ram a b hab := by
    have h₀ (i : ℕ) : 0 ≤ (R.sort (· ≤ ·)).getD i 0 := by
      rcases lt_or_ge i (R.sort (· ≤ ·)).length with hi | hi
      · rw [List.getD_eq_getElem _ _ hi]
        exact (hR _ ((Multiset.mem_sort _).mp (List.getElem_mem hi))).le
      · rw [List.getD_eq_default _ _ hi]
    dsimp only
    split_ifs with ha hb hb
    · exact le_rfl
    · exact h₀ _
    · omega
    rcases Nat.eq_zero_or_pos (Multiset.card R) with hw | hw
    · rw [Multiset.card_eq_zero.mp hw, Multiset.sort_zero]
      exact le_rfl
    have hi : min a (Multiset.card R) - 1 < (R.sort (· ≤ ·)).length := by
      rw [Multiset.length_sort]
      omega
    have hj : min b (Multiset.card R) - 1 < (R.sort (· ≤ ·)).length := by
      rw [Multiset.length_sort]
      omega
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
    exact (Multiset.pairwise_sort R (· ≤ ·)).rel_get_of_le (a := ⟨_, hi⟩) (b := ⟨_, hj⟩)
      (Fin.mk_le_mk.mpr (by omega))
  ram_of_le k hk := by
    rcases Nat.eq_zero_or_pos (Multiset.card R) with hw | hw
    · rw [Multiset.card_eq_zero.mp hw, Multiset.sort_zero]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), min_eq_right hk, min_self]
  ε_pos := Nat.ordCompl_pos p he
  f_pos := hf
  not_dvd_ε := Nat.not_dvd_ordCompl hp he

lemma ram_ofRams (hk₀ : 1 ≤ k) (hk : k ≤ Multiset.card R) : (ofRams p hp R hR e f he hf).ram k =
    (R.sort (· ≤ ·))[k - 1]'(by rw [Multiset.length_sort]; omega) := by
  rw [← List.getD_eq_getElem _ 0]
  exact (ite_eq_right (by omega)).trans (by rw [min_eq_left hk])

variable {a} in
lemma ram_countP_le (ha : 0 ≤ a) : (ofRams p hp R hR e f he hf).ram (R.countP (· ≤ a)) ≤ a := by
  have hc : (R.sort (· ≤ ·)).countP (· ≤ a) = R.countP (· ≤ a) := by
    rw [← Multiset.coe_countP, Multiset.sort_eq]
  rcases Nat.eq_zero_or_pos (R.countP (· ≤ a)) with h | h
  · rw [h]
    exact ha
  rw [ram_ofRams p hp R hR e f he hf h (Multiset.countP_le_card _ _)]
  exact getElem_le_of_lt_countP a (Multiset.pairwise_sort R _) _ (by omega)

variable {a} in
lemma lt_ram_countP_le_add_one (h : R.countP (· ≤ a) < Multiset.card R) :
    a < (ofRams p hp R hR e f he hf).ram (R.countP (· ≤ a) + 1) := by
  have hc : (R.sort (· ≤ ·)).countP (· ≤ a) = R.countP (· ≤ a) := by
    rw [← Multiset.coe_countP, Multiset.sort_eq]
  rw [ram_ofRams p hp R hR e f he hf (by omega) h]
  exact lt_getElem_of_countP_le a (Multiset.pairwise_sort R _) _ (by omega)

lemma ram_ofRams_mem (hk₀ : 1 ≤ k) (hk : k ≤ Multiset.card R) :
    (ofRams p hp R hR e f he hf).ram k ∈ R := by
  rw [ram_ofRams p hp R hR e f he hf hk₀ hk]
  exact (Multiset.mem_sort _).mp (List.getElem_mem _)

variable {p} in
lemma herbrandFunction_zero (I : HerbrandInvariant p) : I.herbrandFunction 0 = 0 := by
  rcases Nat.eq_zero_or_pos I.w with hw | hw
  · rw [I.herbrandFunction_of_le (by rw [hw, I.ram_zero, Rat.cast_zero]), hw, I.ram_zero]
    simp [swanSlope]
  · rw [I.herbrandFunction_of_mem_Icc hw ⟨by rw [I.ram_zero, Rat.cast_zero],
      (I.ram_le_ram (Nat.zero_le 1)).trans' (by rw [I.ram_zero, Rat.cast_zero])⟩, I.ram_zero]
    simp [swanSlope]

end HerbrandInvariant

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  (H : Subgroup (M ≃ₐ[K] M)) {r : ℚ} (i t : ℕ)

/-- The **Herbrand function** `φ_{M/M^H}(i) = (#H_1 + ⋯ + #H_i) / #H_0` of `M` over the fixed field
of a subgroup `H` of `G = Gal(M / K)`, for a finite Galois extension `M / K` of nonarchimedean local
fields, at a natural number `i`, where `H_j = H ∩ G_j` is the `j`-th lower ramification group of
`M / M^H` (Serre, *Local Fields*, IV, Proposition 2). In a tower `M / L / K` with `H = Gal(M / L)`
it is Tau Ceti's Herbrand function of `M / L`
(`IsNonarchimedeanLocalField.herbrandOfSubgroup_range_restrictScalarsHom`). -/
noncomputable def herbrandOfSubgroup : ℚ :=
  (∑ j ∈ Icc 1 i, (Nat.card ↥(H ⊓ lowerRamificationGroup K M j) : ℚ)) /
    Nat.card ↥(H ⊓ lowerRamificationGroup K M 0)

/-- The **rams** (LMFDB `lf.rams`) of the fixed field `L = M^H` of a subgroup `H` of the Galois
group `G` of a finite Galois extension `M / K` of nonarchimedean local fields of residue
characteristic `p`: Deligne's positive lower ramification breaks of `L / K`, the values
`φ_{M/L}(i) = (#H_1 + ⋯ + #H_i) / #H_0` (`IsNonarchimedeanLocalField.herbrandOfSubgroup`) for the
integers `i ≥ 1`, each repeated `log_p (n_i / n_{i + 1})` times, where `n_i = [G_i : G_i ∩ H]`.
They are the `ψ_{L/K}(s)` for the Swan slopes `s` of `L / K`
(`IsNonarchimedeanLocalField.swanSlopesOfSubgroup_eq_map_herbrandOfTower`), and for `H = 1` the
positive lower jumps of `M / K` (`IsNonarchimedeanLocalField.ramsOfSubgroup_bot`). -/
noncomputable def ramsOfSubgroup : Multiset ℚ :=
  ∑ i ∈ range (largestLowerJump K M).toNat, Multiset.replicate
    (padicValNat (ringChar 𝓀[K])
      (H.relIndex (lowerRamificationGroup K M (i + 1)) /
        H.relIndex (lowerRamificationGroup K M (i + 2))))
    (herbrandOfSubgroup K M H (i + 1))

/-- **The rams of a Galois extension**: for `H = 1`, the rams of `M / K` computed in `M` itself are
the positive lower jumps of `M / K`, `IsNonarchimedeanLocalField.ramsOfIsGalois`. -/
lemma ramsOfSubgroup_bot : ramsOfSubgroup K M ⊥ = (ramsOfIsGalois K M).map (↑) := by
  rw [ramsOfIsGalois, ← Multiset.coe_mapAddMonoidHom, map_sum, ramsOfSubgroup]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate, Subgroup.relIndex_bot_left,
    Subgroup.relIndex_bot_left,
    ← (lowerRamificationGroup K M (i + 2)).relIndex_mul_card (lowerRamificationGroup K M (i + 1)),
    inf_of_le_left (lowerRamificationGroup_antitone K M (by omega)),
    Nat.mul_div_cancel _ Nat.card_pos, herbrandOfSubgroup]
  simp

lemma pos_of_mem_ramsOfSubgroup (hr : r ∈ ramsOfSubgroup K M H) : 0 < r := by
  rcases Multiset.mem_sum.mp hr with ⟨i, -, hi⟩
  rw [Multiset.eq_of_mem_replicate hi, herbrandOfSubgroup]
  exact div_pos (sum_pos (fun j _ ↦ Nat.cast_pos.mpr Nat.card_pos) (nonempty_Icc.mpr (by omega)))
    (Nat.cast_pos.mpr Nat.card_pos)

lemma herbrandOfSubgroup_zero : herbrandOfSubgroup K M H 0 = 0 := by
  simp [herbrandOfSubgroup]

lemma herbrandOfSubgroup_succ : herbrandOfSubgroup K M H (t + 1) = herbrandOfSubgroup K M H t +
    Nat.card ↥(H ⊓ lowerRamificationGroup K M (t + 1 : ℕ)) /
        Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) := by
  rw [herbrandOfSubgroup, herbrandOfSubgroup, sum_Icc_succ_top (by omega), add_div]

lemma herbrandOfSubgroup_strictMono : StrictMono (herbrandOfSubgroup K M H) :=
  strictMono_nat_of_lt_succ fun t ↦ by
    rw [herbrandOfSubgroup_succ]
    exact lt_add_of_pos_right _ <| div_pos (Nat.cast_pos.mpr Nat.card_pos)
      (Nat.cast_pos.mpr Nat.card_pos)

lemma countP_le_herbrandOfSubgroup :
    (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) =
      ∑ i ∈ range (largestLowerJump K M).toNat, if i + 1 ≤ t then padicValNat (ringChar 𝓀[K])
        (H.relIndex (lowerRamificationGroup K M (i + 1)) /
          H.relIndex (lowerRamificationGroup K M (i + 2))) else 0 := by
  rw [ramsOfSubgroup, ← Multiset.coe_countPAddMonoidHom, map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Multiset.coe_countPAddMonoidHom, ← Multiset.coe_replicate, Multiset.coe_countP,
    List.countP_replicate]
  simp only [decide_eq_true_eq, (herbrandOfSubgroup_strictMono K M H).le_iff_le]

variable [IsGalois K M] (f : ℕ) (hf : 0 < f)

/-- The **Swan slopes** (LMFDB `lf.swan_slopes`) of the fixed field `L = M^H` of a subgroup `H` of
the Galois group `G` of a finite Galois extension `M / K` of nonarchimedean local fields of residue
characteristic `p`: Deligne's positive upper ramification breaks of `L / K`, the `v > 0` at which
the size `n^v = [G^v : G^v ∩ H]` of the orbits of `G^v` on `G / H ≅ Hom_K(L, M)` drops, with
multiplicity `m` for a drop by `p ^ m`
(`IsNonarchimedeanLocalField.relIndex_upperRamificationGroup_eq_pow_countP`). As
`G^{φ(i)} = G_i` and `G^{φ(i)+} = G_{i + 1}`, they are the `φ_{M/K}(i)` for the integers `i ≥ 1`,
each repeated `log_p (n_i / n_{i + 1})` times with `n_i = [G_i : G_i ∩ H]`, which is the
definition. They do not depend on `M`
(`IsNonarchimedeanLocalField.swanSlopesOfSubgroup_comap_restrictNormalHom`). LMFDB `lf.swan_slopes`
says "nonnegative upper ramification breaks" and "subtracting 1 from each of the positive Artin
slopes", which both admit the tame break `0` (the Artin slope `1`), to which no multiplicity
`log_p` applies; but the tame break is not a Swan slope (LMFDB `lf.slopes`: "the positive upper
ramification jumps", and LMFDB `lf.herbrand_invariant` has `w = v_p(e)` of them), and these slopes
are positive. -/
noncomputable def swanSlopesOfSubgroup : Multiset ℝ :=
  ∑ i ∈ range (largestLowerJump K M).toNat, Multiset.replicate
    (padicValNat (ringChar 𝓀[K])
      (H.relIndex (lowerRamificationGroup K M (i + 1)) /
        H.relIndex (lowerRamificationGroup K M (i + 2))))
    (herbrand K M ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩)

/-- **The Swan slopes of a Galois extension**: for `H = 1`, the Swan slopes of `M / K` are those of
the Galois extension `M / K`, `IsNonarchimedeanLocalField.swanSlopesOfIsGalois`. -/
lemma swanSlopesOfSubgroup_bot : swanSlopesOfSubgroup K M ⊥ = swanSlopesOfIsGalois K M := by
  rw [swanSlopesOfIsGalois, wildArtinSlopesOfIsGalois, ← Multiset.coe_mapAddMonoidHom, map_sum,
    swanSlopesOfSubgroup]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate, add_sub_cancel_left,
    Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    ← (lowerRamificationGroup K M (i + 2)).relIndex_mul_card (lowerRamificationGroup K M (i + 1)),
    inf_of_le_left (lowerRamificationGroup_antitone K M (by omega)),
    Nat.mul_div_cancel _ Nat.card_pos]

lemma pos_of_mem_swanSlopesOfSubgroup {s : ℝ} (hs : s ∈ swanSlopesOfSubgroup K M H) : 0 < s := by
  rcases Multiset.mem_sum.mp hs with ⟨i, -, hi⟩
  have h : herbrand K M ⟨0, by norm_num⟩ <
      herbrand K M ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩ :=
    herbrand_strictMono K M (Subtype.mk_lt_mk.mpr (by positivity))
  rw [herbrand_of_coe_le_zero K M le_rfl] at h
  rw [Multiset.eq_of_mem_replicate hi]
  exact h

variable {i} in
lemma exists_relIndex_lowerRamificationGroup_eq_pow (hi : 1 ≤ i) :
    ∃ k, H.relIndex (lowerRamificationGroup K M i) = ringChar 𝓀[K] ^ k := by
  have h : H.relIndex (lowerRamificationGroup K M i) ∣
      ringChar 𝓀[K] ^ (ramificationIndex K M).factorization (ringChar 𝓀[K]) :=
    natCard_lowerRamificationGroup_one K M ▸ (H.relIndex_dvd_card _).trans
      (Subgroup.card_dvd_of_le <| lowerRamificationGroup_antitone K M <| Nat.one_le_cast.mpr hi)
  rcases (Nat.dvd_prime_pow (CharP.prime_ringChar _)).mp h with ⟨k, -, hk⟩
  exact ⟨k, hk⟩

lemma relIndex_lowerRamificationGroup_eq_pow_sum {j : ℕ} (hj : 1 ≤ j) :
    H.relIndex (lowerRamificationGroup K M j) = ringChar 𝓀[K] ^
      ∑ i ∈ range (largestLowerJump K M).toNat, if j ≤ i + 1 then padicValNat (ringChar 𝓀[K])
        (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
          H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) else 0 := by
  have hp : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  refine eq_pow_sum_padicValNat_div (ringChar 𝓀[K])
    (fun i ↦ H.relIndex (lowerRamificationGroup K M i)) (largestLowerJump K M).toNat
    (fun i hi ↦ exists_relIndex_lowerRamificationGroup_eq_pow K M H hi) (fun i ↦ ?_) ?_ hj
  · exact Subgroup.relIndex_le_of_le_right (lowerRamificationGroup_antitone K M (by omega))
      Subgroup.index_ne_zero_of_finite
  · rw [lowerRamificationGroup_eq_bot_of_largestLowerJump_lt (by omega),
      Subgroup.relIndex_bot_right]

/-- **Deligne's description of the Swan slopes**: for `v > 0`, the size `[G^v : G^v ∩ H]` of the
orbits of the upper ramification group `G^v` on `G / H` is `p ^ N(v)`, where `N(v)` is the number
of Swan slopes `≥ v`, counted with multiplicity. So the number `[G : H] / p ^ N(v)` of orbits of
`G^v` on `G / H` changes exactly at the Swan slopes, by the factor `p ^ m` at a Swan slope of
multiplicity `m`; and these counts determine a multiset of positive reals. -/
lemma relIndex_upperRamificationGroup_eq_pow_countP {v : RamificationIndexDomain}
    (hv : 0 < (v : ℝ)) : H.relIndex (upperRamificationGroup K M v) =
      ringChar 𝓀[K] ^ (swanSlopesOfSubgroup K M H).countP ((v : ℝ) ≤ ·) := by
  have hψ : 0 < (inverseHerbrand K M v : ℝ) := by
    have h : inverseHerbrand K M ⟨0, by norm_num⟩ < inverseHerbrand K M v :=
      inverseHerbrand_strictMono K M (Subtype.mk_lt_mk.mpr hv)
    rwa [inverseHerbrand_of_coe_le_zero K M le_rfl] at h
  have key (i : ℕ) : (v : ℝ) ≤ herbrand K M ⟨(i : ℕ), Nat.cast_mem_ramificationIndexDomain i⟩ ↔
      ⌈(inverseHerbrand K M v : ℝ)⌉₊ ≤ i := by
    rw [Subtype.coe_le_coe, ← (inverseHerbrand_strictMono K M).le_iff_le, inverseHerbrand_herbrand,
      ← Subtype.coe_le_coe]
    exact Nat.ceil_le.symm
  rw [upperRamificationGroup_def, lowerRamificationGroupReal_def,
    ← Int.natCast_ceil_eq_ceil hψ.le, swanSlopesOfSubgroup, ← Multiset.coe_countPAddMonoidHom,
    map_sum, relIndex_lowerRamificationGroup_eq_pow_sum K M H (Nat.ceil_pos.mpr hψ)]
  refine congrArg _ <| sum_congr rfl fun i _ ↦ ?_
  rw [Multiset.coe_countPAddMonoidHom, ← Multiset.coe_replicate, Multiset.coe_countP,
    List.countP_replicate]
  simp only [decide_eq_true_eq, key]
  push_cast
  rfl

/-- **The number of Swan slopes**: `G / H` has `v_p([G_0 : G_0 ∩ H])` Swan slopes, counted with
multiplicity, where `[G_0 : G_0 ∩ H]` is the ramification index of `M^H / K`
(`IsNonarchimedeanLocalField.relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom`). -/
lemma card_swanSlopesOfSubgroup : Multiset.card (swanSlopesOfSubgroup K M H) =
    (H.relIndex (lowerRamificationGroup K M 0)).factorization (ringChar 𝓀[K]) := by
  have hp : (ringChar 𝓀[K]).Prime := CharP.prime_ringChar _
  have h01 : lowerRamificationGroup K M 1 ≤ lowerRamificationGroup K M 0 :=
    lowerRamificationGroup_antitone K M zero_le_one
  have hG : Nat.card ↥(lowerRamificationGroup K M 1) =
      ringChar 𝓀[K] ^ (Nat.card ↥(lowerRamificationGroup K M 0)).factorization (ringChar 𝓀[K]) := by
    rw [natCard_lowerRamificationGroup_one, natCard_lowerRamificationGroup_zero]
  have hI : (H ⊓ lowerRamificationGroup K M 1).relIndex (H ⊓ lowerRamificationGroup K M 0) *
      Nat.card ↥(H ⊓ lowerRamificationGroup K M 1) =
        Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) := by
    have h : (H ⊓ lowerRamificationGroup K M 1).relIndex (H ⊓ lowerRamificationGroup K M 0) *
        Nat.card ↥(H ⊓ lowerRamificationGroup K M 1 ⊓ (H ⊓ lowerRamificationGroup K M 0)) =
          Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) :=
      Subgroup.relIndex_mul_card _ _
    rwa [inf_of_le_left (inf_le_inf_left H h01)] at h
  have hq : (lowerRamificationGroup K M 1).relIndex (lowerRamificationGroup K M 0) =
      ordCompl[ringChar 𝓀[K]] (Nat.card ↥(lowerRamificationGroup K M 0)) := by
    have h : (lowerRamificationGroup K M 1).relIndex (lowerRamificationGroup K M 0) *
        Nat.card ↥(lowerRamificationGroup K M 1 ⊓ lowerRamificationGroup K M 0) =
          Nat.card ↥(lowerRamificationGroup K M 0) :=
      Subgroup.relIndex_mul_card _ _
    rw [inf_of_le_left h01, hG] at h
    exact (Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _) h.symm).symm
  have hr : ¬ringChar 𝓀[K] ∣
      (H ⊓ lowerRamificationGroup K M 1).relIndex (H ⊓ lowerRamificationGroup K M 0) := by
    have h' : H ⊓ lowerRamificationGroup K M 1 ⊓ (H ⊓ lowerRamificationGroup K M 0) =
        lowerRamificationGroup K M 1 ⊓ (H ⊓ lowerRamificationGroup K M 0) := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    have h : (H ⊓ lowerRamificationGroup K M 1).relIndex (H ⊓ lowerRamificationGroup K M 0) =
        (lowerRamificationGroup K M 1).relIndex
          ((H ⊓ lowerRamificationGroup K M 0) ⊔ lowerRamificationGroup K M 1) := by
      rw [Subgroup.relIndex_sup_right, Subgroup.relIndex, Subgroup.relIndex,
        Subgroup.subgroupOf_inj.mpr h']
    have hd : (H ⊓ lowerRamificationGroup K M 1).relIndex (H ⊓ lowerRamificationGroup K M 0) ∣
        (lowerRamificationGroup K M 1).relIndex (lowerRamificationGroup K M 0) :=
      h ▸ Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right <|
        sup_le inf_le_right h01)
    exact fun hpd ↦ Nat.not_dvd_ordCompl hp Nat.card_pos.ne' <| hq ▸ hpd.trans hd
  have hne (A B : Subgroup (M ≃ₐ[K] M)) : A.relIndex B ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have e₀ : (H.relIndex (lowerRamificationGroup K M 0)).factorization (ringChar 𝓀[K]) +
      (Nat.card ↥(H ⊓ lowerRamificationGroup K M 0)).factorization (ringChar 𝓀[K]) =
        (Nat.card ↥(lowerRamificationGroup K M 0)).factorization (ringChar 𝓀[K]) := by
    rw [← Finsupp.add_apply, ← Nat.factorization_mul (hne _ _) Nat.card_pos.ne',
      H.relIndex_mul_card]
  have e₁ : (H.relIndex (lowerRamificationGroup K M 1)).factorization (ringChar 𝓀[K]) +
      (Nat.card ↥(H ⊓ lowerRamificationGroup K M 1)).factorization (ringChar 𝓀[K]) =
        (Nat.card ↥(lowerRamificationGroup K M 0)).factorization (ringChar 𝓀[K]) := by
    rw [← Finsupp.add_apply, ← Nat.factorization_mul (hne _ _) Nat.card_pos.ne',
      H.relIndex_mul_card, hG, hp.factorization_pow, Finsupp.single_eq_same]
  have e₂ : (Nat.card ↥(H ⊓ lowerRamificationGroup K M 1)).factorization (ringChar 𝓀[K]) =
      (Nat.card ↥(H ⊓ lowerRamificationGroup K M 0)).factorization (ringChar 𝓀[K]) := by
    rw [← hI, Nat.factorization_mul (hne _ _) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr, zero_add]
  have e₃ : (H.relIndex (lowerRamificationGroup K M (1 : ℕ))).factorization (ringChar 𝓀[K]) =
      ∑ i ∈ range (largestLowerJump K M).toNat, if 1 ≤ i + 1 then padicValNat (ringChar 𝓀[K])
        (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
          H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) else 0 := by
    rw [relIndex_lowerRamificationGroup_eq_pow_sum K M H le_rfl, hp.factorization_pow,
      Finsupp.single_eq_same]
  simp only [le_add_iff_nonneg_left, zero_le, ite_true, Nat.cast_one, Nat.cast_add,
    Nat.cast_ofNat] at e₃
  rw [swanSlopesOfSubgroup, Multiset.card_sum]
  simp only [Multiset.card_replicate]
  omega

lemma card_ramsOfSubgroup :
    Multiset.card (ramsOfSubgroup K M H) = Multiset.card (swanSlopesOfSubgroup K M H) := by
  simp only [ramsOfSubgroup, swanSlopesOfSubgroup, Multiset.card_sum, Multiset.card_replicate]

lemma natCard_lowerRamificationGroup_succ_div :
    (Nat.card ↥(lowerRamificationGroup K M (t + 1 : ℕ)) : ℝ) /
      Nat.card ↥(lowerRamificationGroup K M 0) =
        (Nat.card ↥(H ⊓ lowerRamificationGroup K M (t + 1 : ℕ)) /
          Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) : ℝ) /
        ((ringChar 𝓀[K] : ℝ) ^ (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) *
          (ordCompl[ringChar 𝓀[K]] (H.relIndex (lowerRamificationGroup K M 0)) : ℕ)) := by
  have h₁ : H.relIndex (lowerRamificationGroup K M (t + 1 : ℕ)) *
      Nat.card ↥(H ⊓ lowerRamificationGroup K M (t + 1 : ℕ)) =
        Nat.card ↥(lowerRamificationGroup K M (t + 1 : ℕ)) :=
    H.relIndex_mul_card _
  have h₀ : H.relIndex (lowerRamificationGroup K M 0) *
      Nat.card ↥(H ⊓ lowerRamificationGroup K M 0) = Nat.card ↥(lowerRamificationGroup K M 0) :=
    H.relIndex_mul_card _
  have he : ordCompl[ringChar 𝓀[K]] (H.relIndex (lowerRamificationGroup K M 0)) *
      ringChar 𝓀[K] ^ Multiset.card (ramsOfSubgroup K M H) =
        H.relIndex (lowerRamificationGroup K M 0) := by
    rw [card_ramsOfSubgroup, card_swanSlopesOfSubgroup, mul_comm]
    exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hs : (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) +
      ∑ i ∈ range (largestLowerJump K M).toNat, (if t + 1 ≤ i + 1 then padicValNat (ringChar 𝓀[K])
        (H.relIndex (lowerRamificationGroup K M (i + 1 : ℕ)) /
          H.relIndex (lowerRamificationGroup K M (i + 2 : ℕ))) else 0) =
        Multiset.card (ramsOfSubgroup K M H) := by
    rw [countP_le_herbrandOfSubgroup, ← sum_add_distrib, ramsOfSubgroup, Multiset.card_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Multiset.card_replicate]
    push_cast
    split_ifs <;> omega
  generalize ordCompl[ringChar 𝓀[K]] (H.relIndex (lowerRamificationGroup K M 0)) = E at he ⊢
  rw [← h₁, ← h₀, ← he, relIndex_lowerRamificationGroup_eq_pow_sum K M H (j := t + 1) (by omega),
    ← hs, pow_add]
  push_cast
  field_simp

variable {t} in
lemma herbrandFunction_ofRams_herbrandOfSubgroup : (HerbrandInvariant.ofRams (ringChar 𝓀[K])
    (CharP.prime_ringChar _) (ramsOfSubgroup K M H) (fun _ ↦ pos_of_mem_ramsOfSubgroup K M H)
    (H.relIndex (lowerRamificationGroup K M 0)) f Subgroup.index_ne_zero_of_finite
    hf).herbrandFunction (herbrandOfSubgroup K M H t) =
      herbrand K M ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩ := by
  induction t with
  | zero =>
    rw [herbrand_of_coe_le_zero K M (by simp)]
    simp [herbrandOfSubgroup, HerbrandInvariant.herbrandFunction_zero]
  | succ t ih =>
    have hR : ∀ r ∈ ramsOfSubgroup K M H, 0 < r := fun _ ↦ pos_of_mem_ramsOfSubgroup K M H
    have h₀ : 0 ≤ herbrandOfSubgroup K M H t :=
      herbrandOfSubgroup_zero K M H ▸ (herbrandOfSubgroup_strictMono K M H).monotone t.zero_le
    have hρ : herbrandOfSubgroup K M H t ≤ herbrandOfSubgroup K M H (t + 1) :=
      (herbrandOfSubgroup_strictMono K M H).monotone (Nat.le_succ t)
    set I : HerbrandInvariant (ringChar 𝓀[K]) := HerbrandInvariant.ofRams (ringChar 𝓀[K])
      (CharP.prime_ringChar _) (ramsOfSubgroup K M H) (fun _ ↦ pos_of_mem_ramsOfSubgroup K M H)
      (H.relIndex (lowerRamificationGroup K M 0)) f Subgroup.index_ne_zero_of_finite hf
    have h₁ : I.ram ((ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t)) ≤
        herbrandOfSubgroup K M H t :=
      HerbrandInvariant.ram_countP_le (ringChar 𝓀[K]) (CharP.prime_ringChar _)
        (ramsOfSubgroup K M H) hR (H.relIndex (lowerRamificationGroup K M 0)) f
        Subgroup.index_ne_zero_of_finite hf h₀
    have hw : I.w = Multiset.card (ramsOfSubgroup K M H) := rfl
    have hε : I.ε = ordCompl[ringChar 𝓀[K]] (H.relIndex (lowerRamificationGroup K M 0)) := rfl
    have key : I.herbrandFunction (herbrandOfSubgroup K M H (t + 1)) =
        I.herbrandFunction (herbrandOfSubgroup K M H t) +
          ((herbrandOfSubgroup K M H (t + 1) : ℝ) - herbrandOfSubgroup K M H t) /
            (I.ε * (ringChar 𝓀[K] : ℝ) ^
              (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t)) := by
      rcases (Multiset.countP_le_card (· ≤ herbrandOfSubgroup K M H t)
        (ramsOfSubgroup K M H)).lt_or_eq with hm | hm
      · have h₂ : herbrandOfSubgroup K M H (t + 1) ≤
            I.ram ((ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) + 1) := by
          have hlt : herbrandOfSubgroup K M H t <
              I.ram ((ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) + 1) :=
            HerbrandInvariant.lt_ram_countP_le_add_one (ringChar 𝓀[K]) (CharP.prime_ringChar _)
              (ramsOfSubgroup K M H) hR (H.relIndex (lowerRamificationGroup K M 0)) f
              Subgroup.index_ne_zero_of_finite hf hm
          have hmem : I.ram ((ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) + 1) ∈
              ramsOfSubgroup K M H :=
            HerbrandInvariant.ram_ofRams_mem (ringChar 𝓀[K]) (CharP.prime_ringChar _)
              (ramsOfSubgroup K M H) hR (H.relIndex (lowerRamificationGroup K M 0)) f
              Subgroup.index_ne_zero_of_finite hf (by omega) hm
          rcases Multiset.mem_sum.mp hmem with ⟨i, -, hi⟩
          rw [Multiset.eq_of_mem_replicate hi] at hlt ⊢
          exact (herbrandOfSubgroup_strictMono K M H).monotone
            ((herbrandOfSubgroup_strictMono K M H).lt_iff_lt.mp hlt)
        rw [I.herbrandFunction_of_mem_Icc (hw ▸ hm) ⟨Rat.cast_le.mpr (h₁.trans hρ),
          Rat.cast_le.mpr h₂⟩, I.herbrandFunction_of_mem_Icc (hw ▸ hm) ⟨Rat.cast_le.mpr h₁,
          Rat.cast_le.mpr (hρ.trans h₂)⟩]
        ring1
      · have hwm : I.w = (ramsOfSubgroup K M H).countP (· ≤ herbrandOfSubgroup K M H t) :=
          hw.trans hm.symm
        rw [I.herbrandFunction_of_le (hwm ▸ Rat.cast_le.mpr (h₁.trans hρ)),
          I.herbrandFunction_of_le (hwm ▸ Rat.cast_le.mpr h₁), hwm]
        ring1
    rw [key, ih, coe_herbrand_of_coe_eq_natCast K M (t + 1)
      (u := ⟨(t + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (t + 1)⟩) rfl,
      coe_herbrand_of_coe_eq_natCast K M t (u := ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) rfl,
      sum_Icc_succ_top (by omega), add_div, herbrandOfSubgroup_succ, hε,
      natCard_lowerRamificationGroup_succ_div K M H t]
    push_cast
    ring1

/-- **The Swan slopes of the Herbrand invariant are the Swan slopes**: the Herbrand invariant
`(r_1, …, r_w)_ε^f` with the rams `r_k` of `G / H` and `ε` the prime-to-`p` part of
`[G_0 : G_0 ∩ H]` has as Swan slopes `s_k = ∑_{j < k} (r_{j + 1} - r_j) / (ε p ^ j)`
(`IsNonarchimedeanLocalField.HerbrandInvariant.swanSlope`) exactly the Swan slopes of `G / H`, so
that LMFDB's three representations of the Herbrand invariant agree. Equivalently, Deligne's Herbrand
function has slope `1 / (ε p ^ k)` between `r_k` and `r_{k + 1}`. -/
lemma map_swanSlope_ofRams : (Multiset.range (HerbrandInvariant.ofRams (ringChar 𝓀[K])
    (CharP.prime_ringChar _) (ramsOfSubgroup K M H) (fun _ ↦ pos_of_mem_ramsOfSubgroup K M H)
    (H.relIndex (lowerRamificationGroup K M 0)) f Subgroup.index_ne_zero_of_finite hf).w).map
      (fun k ↦ ((HerbrandInvariant.ofRams (ringChar 𝓀[K]) (CharP.prime_ringChar _)
        (ramsOfSubgroup K M H) (fun _ ↦ pos_of_mem_ramsOfSubgroup K M H)
        (H.relIndex (lowerRamificationGroup K M 0)) f Subgroup.index_ne_zero_of_finite
          hf).swanSlope (k + 1) : ℝ)) = swanSlopesOfSubgroup K M H := by
  have hR : ∀ r ∈ ramsOfSubgroup K M H, 0 < r := fun _ ↦ pos_of_mem_ramsOfSubgroup K M H
  set I : HerbrandInvariant (ringChar 𝓀[K]) := HerbrandInvariant.ofRams (ringChar 𝓀[K])
    (CharP.prime_ringChar _) (ramsOfSubgroup K M H) (fun _ ↦ pos_of_mem_ramsOfSubgroup K M H)
    (H.relIndex (lowerRamificationGroup K M 0)) f Subgroup.index_ne_zero_of_finite hf
  have hw : I.w = Multiset.card (ramsOfSubgroup K M H) := rfl
  have h₁ : (Multiset.range I.w).map (fun k ↦ I.ram (k + 1)) = ramsOfSubgroup K M H := by
    rw [← Multiset.sort_eq (ramsOfSubgroup K M H) (· ≤ ·), ← Multiset.coe_range, Multiset.map_coe]
    congr 1
    refine List.ext_getElem (by rw [List.length_map, List.length_range, hw,
      Multiset.length_sort]) fun k hk _ ↦ ?_
    rw [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at *
    exact (HerbrandInvariant.ram_ofRams (ringChar 𝓀[K]) (CharP.prime_ringChar _)
      (ramsOfSubgroup K M H) hR (H.relIndex (lowerRamificationGroup K M 0)) f
      Subgroup.index_ne_zero_of_finite hf (by omega) (by omega)).trans (by simp)
  have h₂ : ∀ k ∈ Multiset.range I.w, (I.swanSlope (k + 1) : ℝ) =
      I.herbrandFunction (I.ram (k + 1)) := by
    intro k hk
    rw [Multiset.mem_range] at hk
    rcases (Nat.succ_le_of_lt hk).lt_or_eq with h | h
    · rw [I.herbrandFunction_of_mem_Icc h ⟨le_rfl, I.ram_le_ram (Nat.le_succ _)⟩, sub_self,
        zero_div, add_zero]
    · rw [I.herbrandFunction_of_le (h ▸ le_rfl), ← h, sub_self, zero_div, add_zero]
  have hS : (ramsOfSubgroup K M H).map (fun r : ℚ ↦ I.herbrandFunction r) =
      swanSlopesOfSubgroup K M H := by
    rw [ramsOfSubgroup, ← Multiset.coe_mapAddMonoidHom, map_sum, swanSlopesOfSubgroup]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate,
      herbrandFunction_ofRams_herbrandOfSubgroup K M H f hf]
  rw [← hS, ← h₁, Multiset.map_map]
  exact Multiset.map_congr rfl h₂

variable (M' : Type*) [Field M'] [ValuativeRel M'] [TopologicalSpace M']
  [IsNonarchimedeanLocalField M'] [Algebra K M'] [ValuativeExtension K M'] [Module.Finite K M']
  [IsGalois K M'] [Algebra M M'] [ValuativeExtension M M'] [Module.Finite M M']
  [IsScalarTower K M M']

/-- **The Swan slopes do not depend on the Galois extension**: for finite Galois extensions
`M' ⊇ M` of `K` and a subgroup `H` of `Gal(M / K)` with preimage `H'` in `Gal(M' / K)`, the fixed
fields `M'^{H'} = M^H` have the same Swan slopes computed in `M'` and in `M`. This follows from
Deligne's description and Herbrand's theorem `G'^v ↦ G^v`. -/
lemma swanSlopesOfSubgroup_comap_restrictNormalHom :
    swanSlopesOfSubgroup K M' (H.comap (AlgEquiv.restrictNormalHom M)) =
      swanSlopesOfSubgroup K M H := by
  refine eq_of_countP_le_eq (fun _ ↦ pos_of_mem_swanSlopesOfSubgroup K M' _)
    (fun _ ↦ pos_of_mem_swanSlopesOfSubgroup K M H) fun v hv ↦ ?_
  have hv' : v ∈ RamificationIndexDomain := Set.mem_Ici.mpr (by linarith)
  refine Nat.pow_right_injective (CharP.prime_ringChar 𝓀[K]).two_le <|
    (relIndex_upperRamificationGroup_eq_pow_countP K M' _ (v := ⟨v, hv'⟩) hv).symm.trans ?_
      |>.trans <| relIndex_upperRamificationGroup_eq_pow_countP K M H (v := ⟨v, hv'⟩) hv
  rw [Subgroup.relIndex_comap, map_restrictNormalHom_upperRamificationGroup]

/-- **The Swan slopes of a Galois subextension**: for finite Galois extensions `M' ⊇ M` of `K`, the
Swan slopes of `M = M'^{Gal(M' / M)}` computed in `M'` are the Swan slopes of the Galois extension
`M / K`, `IsNonarchimedeanLocalField.swanSlopesOfIsGalois`. -/
lemma swanSlopesOfSubgroup_ker_restrictNormalHom :
    swanSlopesOfSubgroup K M' (AlgEquiv.restrictNormalHom M).ker = swanSlopesOfIsGalois K M := by
  rw [← swanSlopesOfSubgroup_bot, ← swanSlopesOfSubgroup_comap_restrictNormalHom K M ⊥ M',
    MonoidHom.comap_bot]

section Tower

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [Algebra L M] [IsScalarTower K L M] [ValuativeExtension L M] [Module.Finite L M]
  {x : ℝ}

/-- **The Herbrand function of the top of a tower**: for a tower `M / L / K` of nonarchimedean local
fields with `M / K` finite Galois and `H = Gal(M / L)`,
`IsNonarchimedeanLocalField.herbrandOfSubgroup` is Tau Ceti's Herbrand function `φ_{M/L}` at the
natural numbers. -/
lemma herbrandOfSubgroup_range_restrictScalarsHom :
    haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
    (herbrandOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range i : ℝ) =
      herbrand L M ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩ := by
  have hL : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have h (j : ℤ) : Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓
      lowerRamificationGroup K M j) = Nat.card ↥(lowerRamificationGroup L M j) := by
    rw [← map_restrictScalarsHom_lowerRamificationGroup K M L,
      Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective K)]
  rw [coe_herbrand_of_coe_eq_natCast L M i rfl, herbrandOfSubgroup]
  push_cast
  simp only [h]

variable [ValuativeExtension K L] in
/-- **The ramification index of an intermediate field**: for a tower `M / L / K` of nonarchimedean
local fields with `M / K` finite Galois and `H = Gal(M / L)`, the index `[G_0 : G_0 ∩ H]` is the
ramification index `e(L / K)`. -/
lemma relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom :
    (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex (lowerRamificationGroup K M 0) =
      ramificationIndex K L := by
  have hL : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have h : (AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex (lowerRamificationGroup K M 0) *
      Nat.card ↥((AlgEquiv.restrictScalarsHom (S := L) K).range ⊓ lowerRamificationGroup K M 0) =
        Nat.card ↥(lowerRamificationGroup K M 0) :=
    Subgroup.relIndex_mul_card _ _
  rw [← map_restrictScalarsHom_lowerRamificationGroup K M L,
    Subgroup.card_map_of_injective (AlgEquiv.restrictScalars_injective K),
    natCard_lowerRamificationGroup_zero, natCard_lowerRamificationGroup_zero,
    ramificationIndex_tower (K := K) (L := L) M] at h
  exact Nat.eq_of_mul_eq_mul_right ramificationIndex_pos h

variable [ValuativeExtension K L] in
/-- **The number of Swan slopes and rams**: for a tower `M / L / K` of nonarchimedean local fields
with `M / K` finite Galois, `L / K` has `w = v_p(e(L / K))` Swan slopes, counted with multiplicity,
as many as rams, where `e(L / K) = ε p ^ w` with `p ∤ ε`. -/
lemma card_swanSlopesOfSubgroup_range_restrictScalarsHom :
    Multiset.card (swanSlopesOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range) =
      (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
  rw [card_swanSlopesOfSubgroup, relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom]

variable (x) in
/-- **Deligne's Herbrand function** `φ_{L/K} = φ_{M/K} ∘ ψ_{M/L}` of a tower `M / L / K` of
nonarchimedean local fields with `M / K` finite Galois, where `L / K` need not be Galois (Serre,
*Local Fields*, IV, §3, and Deligne), extended to `ℝ` by its value `-1` at `-1` below `-1`. -/
noncomputable def herbrandOfTower : ℝ :=
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  herbrand K M (inverseHerbrand L M ⟨max x (-1), le_max_right x (-1)⟩)

/-- **The Swan slopes are the images of the rams under `φ_{L/K}`**: in a tower `M / L / K` with
`M / K` finite Galois, the Swan slopes of `L / K` are the `φ_{L/K}(r)` for the rams `r` of `L / K`,
with the same multiplicities; so the rams are Deligne's lower breaks `ψ_{L/K}(s)`. -/
lemma swanSlopesOfSubgroup_eq_map_herbrandOfTower :
    swanSlopesOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range =
      ((ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).map (↑)).map
        (herbrandOfTower K M L) := by
  have hL : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  rw [Multiset.map_map, ramsOfSubgroup, ← Multiset.coe_mapAddMonoidHom, map_sum,
    swanSlopesOfSubgroup]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Multiset.coe_mapAddMonoidHom, Multiset.map_replicate, Function.comp_apply,
    herbrandOfSubgroup_range_restrictScalarsHom]
  simp only [herbrandOfTower, max_eq_left (Set.mem_Ici.mp (herbrand L M _).2), Subtype.coe_eta,
    inverseHerbrand_herbrand]

variable [ValuativeExtension K L] in
/-- The **Herbrand invariant** `I = (r_1, …, r_w)_ε^f` (LMFDB `lf.herbrand_invariant`) of an
extension `L / K` of nonarchimedean local fields of residue characteristic `p`, computed in a finite
Galois extension `M ⊇ L` of `K`: the rams `r_1 ≤ ⋯ ≤ r_w` of `L / K`
(`IsNonarchimedeanLocalField.ramsOfSubgroup` for `Gal(M / L)`), the prime-to-`p` part `ε` of the
ramification index `e(L / K)` and the residue degree `f` of `L / K`. Then `e(L / K) = ε p ^ w`
(`IsNonarchimedeanLocalField.ε_mul_pow_w_herbrandInvariantOfTower`), and `I` does not depend on `M`
(`IsNonarchimedeanLocalField.herbrandInvariantOfTower_eq`); its Swan slopes, computed from the rams,
are the Swan slopes of `L / K`
(`IsNonarchimedeanLocalField.map_swanSlope_herbrandInvariantOfTower`). Its small rams `r_k^*` and
tiny rams `r_k'` (LMFDB `lf.rams`) are `IsNonarchimedeanLocalField.HerbrandInvariant.smallRam` and
`IsNonarchimedeanLocalField.HerbrandInvariant.tinyRam`. -/
noncomputable def herbrandInvariantOfTower : HerbrandInvariant (ringChar 𝓀[K]) :=
  HerbrandInvariant.ofRams (ringChar 𝓀[K]) (CharP.prime_ringChar _)
    (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range)
    (fun _ ↦ pos_of_mem_ramsOfSubgroup K M _) (ramificationIndex K L) (inertiaDegree K L)
    ramificationIndex_pos.ne' inertiaDegree_pos

variable [ValuativeExtension K L] in
/-- **The ramification index of an extension is `ε p ^ w`**: the tame part `ε` and the number `w` of
rams of the Herbrand invariant of `L / K` satisfy `ε p ^ w = e(L / K)`, so that `w = v_p(e(L / K))`
as LMFDB `lf.herbrand_invariant` presupposes. -/
lemma ε_mul_pow_w_herbrandInvariantOfTower :
    (herbrandInvariantOfTower K M L).ε * ringChar 𝓀[K] ^ (herbrandInvariantOfTower K M L).w =
      ramificationIndex K L := by
  have hw : (herbrandInvariantOfTower K M L).w =
      Multiset.card (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range) :=
    rfl
  have hε : (herbrandInvariantOfTower K M L).ε =
      ordCompl[ringChar 𝓀[K]] (ramificationIndex K L) :=
    rfl
  rw [hw, hε, card_ramsOfSubgroup, card_swanSlopesOfSubgroup_range_restrictScalarsHom, mul_comm]
  exact Nat.ordProj_mul_ordCompl_eq_self _ _

variable [ValuativeExtension K L] in
/-- **The Swan slopes of the Herbrand invariant of `L / K` are the Swan slopes of `L / K`**: the
Swan slopes `s_k = ∑_{j < k} (r_{j + 1} - r_j) / (ε p ^ j)` of the Herbrand invariant
`(r_1, …, r_w)_ε^f` of `L / K` are the Swan slopes of `L / K`, so that the representations
`[s_1, …, s_w]_ε^f` and `(r_1, …, r_w)_ε^f` of LMFDB `lf.herbrand_invariant` agree. -/
lemma map_swanSlope_herbrandInvariantOfTower :
    (Multiset.range (herbrandInvariantOfTower K M L).w).map
      (fun k ↦ ((herbrandInvariantOfTower K M L).swanSlope (k + 1) : ℝ)) =
        swanSlopesOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range := by
  have h : herbrandInvariantOfTower K M L = HerbrandInvariant.ofRams (ringChar 𝓀[K])
      (CharP.prime_ringChar _) (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range)
      (fun _ ↦ pos_of_mem_ramsOfSubgroup K M _)
      ((AlgEquiv.restrictScalarsHom (S := L) K).range.relIndex (lowerRamificationGroup K M 0))
      (inertiaDegree K L) Subgroup.index_ne_zero_of_finite inertiaDegree_pos := by
    rw [herbrandInvariantOfTower]
    congr 1
    exact (relIndex_lowerRamificationGroup_zero_range_restrictScalarsHom K M L).symm
  rw [h]
  exact map_swanSlope_ofRams K M _ _ _

lemma herbrandOfTower_le_herbrandOfTower_iff {y : ℝ} (hx : -1 ≤ x) (hy : -1 ≤ y) :
    herbrandOfTower K M L x ≤ herbrandOfTower K M L y ↔ x ≤ y := by
  have hL : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  simp only [herbrandOfTower, max_eq_left hx, max_eq_left hy, Subtype.coe_le_coe,
    (herbrand_strictMono K M).le_iff_le, (inverseHerbrand_strictMono L M).le_iff_le,
    Subtype.mk_le_mk]

lemma countP_map_herbrandOfTower (hS : ∀ x ∈ S, 0 < x) {u : ℝ} (hu : 0 < u) :
    (S.map (herbrandOfTower K M L)).countP (herbrandOfTower K M L u ≤ ·) = S.countP (u ≤ ·) := by
  rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter]
  exact Multiset.countP_congr rfl fun x hx ↦ propext <|
    herbrandOfTower_le_herbrandOfTower_iff K M L (by linarith) (by linarith [hS x hx])

variable [Algebra L M'] [IsScalarTower K L M'] [ValuativeExtension L M'] [Module.Finite L M']
  [IsScalarTower L M M']

/-- **Deligne's Herbrand function does not depend on the Galois extension**: for finite Galois
extensions `M' ⊇ M ⊇ L` of `K`, `φ_{M'/K} ∘ ψ_{M'/L} = φ_{M/K} ∘ ψ_{M/L}`, by the transitivity of
the Herbrand functions of the Galois towers `M' / M / K` and `M' / M / L`. -/
lemma herbrandOfTower_eq_herbrandOfTower : herbrandOfTower K M' L = herbrandOfTower K M L := by
  have h₁ : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have h₂ : IsGalois L M' := IsGalois.tower_top_of_isGalois K L M'
  funext x
  rw [herbrandOfTower, herbrandOfTower, ← herbrandOrderIso_symm_apply L M',
    inverseHerbrand_tower L M M', OrderIso.trans_apply, ← herbrandOrderIso_apply K M',
    herbrand_tower K M M', OrderIso.trans_apply, OrderIso.apply_symm_apply, herbrandOrderIso_apply,
    herbrandOrderIso_symm_apply]

/-- **The rams do not depend on the Galois extension**: for finite Galois extensions
`M' ⊇ M ⊇ L` of `K`, the rams of `L / K` computed in `M'` and in `M` agree. Both are the
`ψ_{L/K}(s)` for the Swan slopes `s` of `L / K`, which do not depend on the Galois extension, and
neither does `φ_{L/K}`. -/
lemma ramsOfSubgroup_range_restrictScalarsHom_eq :
    ramsOfSubgroup K M' (AlgEquiv.restrictScalarsHom (S := L) K).range =
      ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range := by
  have hL : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have hH : (AlgEquiv.restrictScalarsHom (S := L) K : (M' ≃ₐ[L] M') →* M' ≃ₐ[K] M').range =
      (AlgEquiv.restrictScalarsHom (S := L) K : (M ≃ₐ[L] M) →* M ≃ₐ[K] M).range.comap
        (AlgEquiv.restrictNormalHom M) := by
    ext σ
    simp only [MonoidHom.mem_range]
    constructor
    · rintro ⟨τ, rfl⟩
      refine ⟨τ.restrictNormal M, AlgEquiv.ext fun x ↦ (algebraMap M M').injective ?_⟩
      rw [AlgEquiv.restrictScalarsHom_apply, AlgEquiv.coe_restrictScalars,
        AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
        AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalarsHom_apply,
        AlgEquiv.coe_restrictScalars]
    · rintro ⟨τ, hτ⟩
      refine ⟨({ σ with commutes' := fun l ↦ ?_ } : M' ≃ₐ[L] M'), AlgEquiv.ext fun _ ↦ rfl⟩
      have h : AlgEquiv.restrictNormalHom M σ (algebraMap L M l) = algebraMap L M l := by
        rw [← hτ]
        exact τ.commutes l
      rw [IsScalarTower.algebraMap_apply L M M']
      exact (AlgEquiv.restrictNormal_commutes σ M _).symm.trans (congrArg (algebraMap M M') h)
  have hS : ((ramsOfSubgroup K M' (AlgEquiv.restrictScalarsHom (S := L) K).range).map (↑)).map
      (herbrandOfTower K M L) =
        ((ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).map (↑)).map
          (herbrandOfTower K M L) := by
    rw [← herbrandOfTower_eq_herbrandOfTower K M M' L,
      ← swanSlopesOfSubgroup_eq_map_herbrandOfTower, hH,
      swanSlopesOfSubgroup_comap_restrictNormalHom, herbrandOfTower_eq_herbrandOfTower K M M' L,
      swanSlopesOfSubgroup_eq_map_herbrandOfTower]
  have h' : ∀ x ∈ (ramsOfSubgroup K M' (AlgEquiv.restrictScalarsHom (S := L) K).range).map
      ((↑) : ℚ → ℝ), 0 < x := by
    simp only [Multiset.mem_map]
    rintro _ ⟨r, hr, rfl⟩
    exact Rat.cast_pos.mpr <| pos_of_mem_ramsOfSubgroup K M' _ hr
  have h : ∀ x ∈ (ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range).map
      ((↑) : ℚ → ℝ), 0 < x := by
    simp only [Multiset.mem_map]
    rintro _ ⟨r, hr, rfl⟩
    exact Rat.cast_pos.mpr <| pos_of_mem_ramsOfSubgroup K M _ hr
  refine Multiset.map_injective Rat.cast_injective <| eq_of_countP_le_eq h' h fun u hu ↦ ?_
  rw [← countP_map_herbrandOfTower K M L h' hu, hS, countP_map_herbrandOfTower K M L h hu]

variable [ValuativeExtension K L] in
/-- **The Herbrand invariant does not depend on the Galois extension**: for finite Galois extensions
`M' ⊇ M ⊇ L` of `K`, the Herbrand invariants of `L / K` computed in `M'` and in `M` agree. -/
lemma herbrandInvariantOfTower_eq :
    herbrandInvariantOfTower K M' L = herbrandInvariantOfTower K M L := by
  rw [herbrandInvariantOfTower, herbrandInvariantOfTower]
  congr 1
  exact ramsOfSubgroup_range_restrictScalarsHom_eq K M M' L

variable [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L] in
/-- **The Swan slopes of a Galois subextension**: for a tower `M / L / K` with `L / K` and `M / K`
finite Galois, the Swan slopes of `L / K` computed in `M` are the Swan slopes of the Galois
extension `L / K`, `IsNonarchimedeanLocalField.swanSlopesOfIsGalois`. -/
lemma swanSlopesOfSubgroup_range_restrictScalarsHom_of_isGalois :
    swanSlopesOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range =
      swanSlopesOfIsGalois K L := by
  rw [AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M,
    swanSlopesOfSubgroup_ker_restrictNormalHom K L M]

variable [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L] in
/-- **The rams of a Galois subextension**: for a tower `M / L / K` with `L / K` and `M / K` finite
Galois, the rams of `L / K` computed in `M` are the rams of the Galois extension `L / K`,
`IsNonarchimedeanLocalField.ramsOfIsGalois`. -/
lemma ramsOfSubgroup_range_restrictScalarsHom_of_isGalois :
    ramsOfSubgroup K M (AlgEquiv.restrictScalarsHom (S := L) K).range =
      (ramsOfIsGalois K L).map (↑) := by
  have h : ValuativeExtension L L := ⟨fun _ _ ↦ Iff.rfl⟩
  rw [ramsOfSubgroup_range_restrictScalarsHom_eq K L M L,
    MonoidHom.range_eq_bot_iff.mpr (Subsingleton.elim _ _), ramsOfSubgroup_bot]

end Tower

variable {K} (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]

variable [Algebra.IsSeparable K L] in
/-- **The Swan slopes of an extension inside `K̄` are Deligne's**: LeanBridge's
`IsNonarchimedeanLocalField.visibleSwanSlopes` of a finite separable extension `L` of `K` inside
`K̄` are the Swan slopes of `L = M^H` for its Galois closure `M` in `K̄` and `H = Gal(M / L)`. -/
lemma visibleSwanSlopes_eq_swanSlopesOfSubgroup :
    letI : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
    letI : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
    haveI : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ _
    haveI : ValuativeExtension K (Algebra.galoisClosure K L) :=
      finiteIntermediateField_valuativeExtension K _ _
    visibleSwanSlopes L = swanSlopesOfSubgroup K (Algebra.galoisClosure K L)
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)) :=
  rfl

/-- The **rams** (LMFDB `lf.rams`) of a finite separable extension `L` of a nonarchimedean local
field `K` inside `K̄`, which need not be Galois: Deligne's positive lower ramification breaks, the
rams `IsNonarchimedeanLocalField.ramsOfSubgroup` of `L = M^H` for the Galois closure `M` of `L` in
`K̄` and `H = Gal(M / L)`, with Tau Ceti's spectral-norm local-field structure on `M`. They are
rational numbers, and the `ψ_{L/K}(s)` for the Swan slopes `s` of `L / K`. -/
noncomputable def visibleRams : Multiset ℚ :=
  letI : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  letI : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  haveI : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  haveI : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  ramsOfSubgroup K (Algebra.galoisClosure K L)
    (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L))

lemma pos_of_mem_visibleRams (hr : r ∈ visibleRams L) : 0 < r := by
  let v : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  let t : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  have h : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have h' : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  exact pos_of_mem_ramsOfSubgroup K _ _ hr

/-- The **Herbrand invariant** `I = (r_1, …, r_w)_ε^f` (LMFDB `lf.herbrand_invariant`) of a finite
separable extension `L` of a nonarchimedean local field `K` inside `K̄`, at the residue
characteristic `p` of `K`: the rams `r_1 ≤ ⋯ ≤ r_w` of `L / K`
(`IsNonarchimedeanLocalField.visibleRams`), the prime-to-`p` part `ε` of the ramification index
`e(L / K)` and the residue degree `f` of `L / K`, for Tau Ceti's spectral-norm local-field structure
on `L`. Its small rams `r_k^*` and tiny rams `r_k'` (LMFDB `lf.rams`) are
`IsNonarchimedeanLocalField.HerbrandInvariant.smallRam` and
`IsNonarchimedeanLocalField.HerbrandInvariant.tinyRam`. Here `w` is the number of rams, and
`e(L / K) = ε p ^ w` (`IsNonarchimedeanLocalField.ε_mul_pow_w_visibleHerbrandInvariant`); for a
`p`-adic field `K`, `L` has this Herbrand invariant in the sense of
`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf`
(`IsNonarchimedeanLocalField.isInvariantOf_visibleHerbrandInvariant`). -/
noncomputable def visibleHerbrandInvariant : HerbrandInvariant (ringChar 𝓀[K]) :=
  letI : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  letI : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  haveI : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  haveI : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  HerbrandInvariant.ofRams (ringChar 𝓀[K]) (CharP.prime_ringChar _) (visibleRams L)
    (fun _ ↦ pos_of_mem_visibleRams L) (ramificationIndex K L) (inertiaDegree K L)
    ramificationIndex_pos.ne' inertiaDegree_pos

variable [Algebra.IsSeparable K L] in
/-- **The number of Swan slopes of an extension inside `K̄`**: a finite separable extension `L` of
`K` inside `K̄` has `v_p(e(L / K))` Swan slopes, counted with multiplicity, for Tau Ceti's
spectral-norm local-field structure on `L`. -/
lemma card_visibleSwanSlopes :
    letI : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
    letI : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
    haveI : IsNonarchimedeanLocalField L :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ L
    haveI : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
    Multiset.card (visibleSwanSlopes L) =
      (ramificationIndex K L).factorization (ringChar 𝓀[K]) := by
  let vL : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  let tL : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  have hL : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  have hKL : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  let vM : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hLM : L ≤ Algebra.galoisClosure K L :=
    Algebra.galoisClosure_eq_normalClosure (F := K) L ▸ L.le_normalClosure
  let a : Algebra L (Algebra.galoisClosure K L) := (IntermediateField.inclusion hLM).toAlgebra
  have hs : IsScalarTower K L (Algebra.galoisClosure K L) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension L (Algebra.galoisClosure K L) :=
    (IntermediateField.inclusion hLM).valuativeExtension
  have hf : Module.Finite L (Algebra.galoisClosure K L) :=
    .of_restrictScalars_finite K L _
  rw [visibleSwanSlopes_eq_swanSlopesOfSubgroup,
    fixingSubgroup_preimage_eq_range_restrictScalarsHom hLM]
  exact card_swanSlopesOfSubgroup_range_restrictScalarsHom K _ L

variable [Algebra.IsSeparable K L] in
/-- **The ramification index of an extension inside `K̄` is `ε p ^ w`**: the tame part `ε` and the
number `w` of rams of the Herbrand invariant of a finite separable extension `L` of `K` inside `K̄`
satisfy `ε p ^ w = e(L / K)`, so that `w = v_p(e(L / K))` as LMFDB `lf.herbrand_invariant`
presupposes. -/
lemma ε_mul_pow_w_visibleHerbrandInvariant :
    letI : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
    letI : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
    haveI : IsNonarchimedeanLocalField L :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ L
    haveI : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
    (visibleHerbrandInvariant L).ε * ringChar 𝓀[K] ^ (visibleHerbrandInvariant L).w =
      ramificationIndex K L := by
  let vL : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  let tL : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  have hL : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  have hKL : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  let vM : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hw : (visibleHerbrandInvariant L).w = Multiset.card (visibleSwanSlopes L) :=
    card_ramsOfSubgroup K _ _
  have hε : (visibleHerbrandInvariant L).ε =
      ordCompl[ringChar 𝓀[K]] (ramificationIndex K L) :=
    rfl
  rw [hw, hε, card_visibleSwanSlopes, mul_comm]
  exact Nat.ordProj_mul_ordCompl_eq_self _ _

variable [IsGalois K L] in
/-- **The Swan slopes of a Galois extension inside `K̄`**: for `L / K` Galois, the Swan slopes of
`L` computed in its Galois closure in `K̄` are the Swan slopes
`IsNonarchimedeanLocalField.swanSlopesOfIsGalois` of the Galois extension `L / K`. -/
lemma visibleSwanSlopes_eq_swanSlopesOfIsGalois :
    letI : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
    letI : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
    haveI : IsNonarchimedeanLocalField L :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ L
    haveI : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
    visibleSwanSlopes L = swanSlopesOfIsGalois K L := by
  let vL : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  let tL : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  have hL : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  have hKL : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  let vM : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hLM : L ≤ Algebra.galoisClosure K L :=
    Algebra.galoisClosure_eq_normalClosure (F := K) L ▸ L.le_normalClosure
  let a : Algebra L (Algebra.galoisClosure K L) := (IntermediateField.inclusion hLM).toAlgebra
  have hs : IsScalarTower K L (Algebra.galoisClosure K L) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension L (Algebra.galoisClosure K L) :=
    (IntermediateField.inclusion hLM).valuativeExtension
  have hf : Module.Finite L (Algebra.galoisClosure K L) :=
    .of_restrictScalars_finite K L _
  rw [visibleSwanSlopes_eq_swanSlopesOfSubgroup,
    fixingSubgroup_preimage_eq_range_restrictScalarsHom hLM]
  exact swanSlopesOfSubgroup_range_restrictScalarsHom_of_isGalois K _ L

variable [IsGalois K L] in
/-- **The rams of a Galois extension inside `K̄`**: for `L / K` Galois, the rams of `L` computed in
its Galois closure in `K̄` are the rams `IsNonarchimedeanLocalField.ramsOfIsGalois` of the Galois
extension `L / K`, its positive lower jumps. -/
lemma visibleRams_eq_ramsOfIsGalois :
    letI : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
    letI : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
    haveI : IsNonarchimedeanLocalField L :=
      finiteIntermediateField_isNonarchimedeanLocalField K _ L
    haveI : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
    visibleRams L = (ramsOfIsGalois K L).map (↑) := by
  let vL : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  let tL : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  have hL : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  have hKL : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  let vM : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hLM : L ≤ Algebra.galoisClosure K L :=
    Algebra.galoisClosure_eq_normalClosure (F := K) L ▸ L.le_normalClosure
  let a : Algebra L (Algebra.galoisClosure K L) := (IntermediateField.inclusion hLM).toAlgebra
  have hs : IsScalarTower K L (Algebra.galoisClosure K L) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension L (Algebra.galoisClosure K L) :=
    (IntermediateField.inclusion hLM).valuativeExtension
  have hf : Module.Finite L (Algebra.galoisClosure K L) :=
    .of_restrictScalars_finite K L _
  rw [visibleRams, fixingSubgroup_preimage_eq_range_restrictScalarsHom hLM]
  exact ramsOfSubgroup_range_restrictScalarsHom_of_isGalois K _ L

variable [CharZero K] in
/-- **An extension inside `K̄` belongs to the family of its Herbrand invariant**: a finite extension
`L` of a `p`-adic field `K` inside `K̄` has the Herbrand invariant
`IsNonarchimedeanLocalField.visibleHerbrandInvariant L` in the sense of
`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf`: its residue degree is `f`, its
ramification index is `ε p ^ w` and its Swan slopes are the Swan slopes `s_1, …, s_w` of the
invariant, computed from its rams by LMFDB's formula. So `L` lies in the family `I / K` of its
invariant `I`. -/
lemma isInvariantOf_visibleHerbrandInvariant : (visibleHerbrandInvariant L).IsInvariantOf K L := by
  rw [HerbrandInvariant.IsInvariantOf]
  refine ⟨rfl, (ε_mul_pow_w_visibleHerbrandInvariant L).symm, ?_⟩
  let vL : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  let tL : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  have hL : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  have hKL : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  let vM : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  let tM : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  have hM : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  have hKM : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hLM : L ≤ Algebra.galoisClosure K L :=
    Algebra.galoisClosure_eq_normalClosure (F := K) L ▸ L.le_normalClosure
  let a : Algebra L (Algebra.galoisClosure K L) := (IntermediateField.inclusion hLM).toAlgebra
  have hs : IsScalarTower K L (Algebra.galoisClosure K L) := .of_algebraMap_eq fun _ ↦ rfl
  have hv : ValuativeExtension L (Algebra.galoisClosure K L) :=
    (IntermediateField.inclusion hLM).valuativeExtension
  have hf : Module.Finite L (Algebra.galoisClosure K L) :=
    .of_restrictScalars_finite K L _
  have hI :
      visibleHerbrandInvariant L = herbrandInvariantOfTower K (Algebra.galoisClosure K L) L := by
    rw [visibleHerbrandInvariant, herbrandInvariantOfTower]
    congr 1
    rw [visibleRams, fixingSubgroup_preimage_eq_range_restrictScalarsHom hLM]
  rw [visibleSwanSlopes_eq_swanSlopesOfSubgroup,
    fixingSubgroup_preimage_eq_range_restrictScalarsHom hLM, hI]
  exact (map_swanSlope_herbrandInvariantOfTower K _ L).symm

variable [CharZero K] in
/-- **Every extension lies in the family of its Herbrand invariant**: the `K`-isomorphism class of a
finite extension `E` of a `p`-adic field `K` lies in the family `I / K` (LMFDB
`lf.family_polynomial`) of its Herbrand invariant `I`, so the families cover all extensions. -/
lemma mk_mem_family_visibleHerbrandInvariant (E : FiniteExtension K) :
    haveI : FiniteDimensional K E.1 := E.2
    Quotient.mk _ E ∈ (visibleHerbrandInvariant E.1).family K := by
  have h : FiniteDimensional K E.1 := E.2
  exact ⟨E, isInvariantOf_visibleHerbrandInvariant E.1, rfl⟩

end IsNonarchimedeanLocalField
